module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 022. -/

theorem predecessorHalfFin13_clause10264 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0714 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10265 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0714 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10269 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0714 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10271 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      ¬PredecessorHalfFin13Atom0209 chi ∧
      PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0714 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10272 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0145 chi ∧
      PredecessorHalfFin13Atom0209 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0131 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0145
    PredecessorHalfFin13Atom0209 PredecessorHalfFin13Atom0714 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10273 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10274 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10275 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10276 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10277 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10278 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10279 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10280 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10281 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10282 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10284 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10288 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10289 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10292 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10293 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10294 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10295 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10296 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0146 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0146
    PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0715 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10297 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10298 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10299 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10300 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10301 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10302 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10303 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10304 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10305 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10306 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10308 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10310 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10312 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10313 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10315 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10317 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10319 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      ¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10320 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0147 chi ∧
      PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0147
    PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0716 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10321 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10322 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10323 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10324 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10325 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10326 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10327 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10328 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10329 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0717 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10330 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0717 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10332 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0717 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10336 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0717 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10337 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0717 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10341 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0717 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10343 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0717 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10344 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0148 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0135 PredecessorHalfFin13Atom0148
    PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0717 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10345 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10346 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10347 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10348 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10349 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10350 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10351 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10352 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10353 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0718 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10354 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0718 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10356 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0718 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10360 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0718 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10361 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0718 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10363 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0718 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10365 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0718 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10367 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0718 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10368 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      PredecessorHalfFin13Atom0149 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0136 PredecessorHalfFin13Atom0149
    PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0718 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10369 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10370 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10371 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10372 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10373 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10374 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10375 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10376 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10377 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0719 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10378 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0719 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10380 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0719 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10384 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0719 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10385 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0719 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10389 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      ¬PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0719 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10391 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0719 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10392 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0137 chi ∧
      PredecessorHalfFin13Atom0150 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0137 PredecessorHalfFin13Atom0150
    PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0719 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10393 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10394 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10395 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10396 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10397 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10398 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10399 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10400 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10401 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10402 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10404 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10408 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10409 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10411 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10412 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10413 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      ¬PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10415 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10416 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0138 chi ∧
      PredecessorHalfFin13Atom0151 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0132 PredecessorHalfFin13Atom0138 PredecessorHalfFin13Atom0151
    PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0720 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10417 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10418 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10419 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10420 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10421 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10422 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10423 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10424 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10425 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10426 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10427 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10428 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10432 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10433 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10436 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10437 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10439 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      ¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10440 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0152 chi ∧
      PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0133 PredecessorHalfFin13Atom0134 PredecessorHalfFin13Atom0152
    PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0721 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10441 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
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

theorem predecessorHalfFin13_clause10442 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0153 chi ∧
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

end ErdosSzekeres

end
