module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 055. -/

theorem predecessorHalfFin13_clause16110 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16111 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16112 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16113 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0958 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16116 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0958 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16120 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0958 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16121 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0958 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16125 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0958 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16127 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0958 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16128 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0958 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16129 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16130 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16131 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16132 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16133 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16134 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16135 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16136 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16137 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0959 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16138 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0959 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16140 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0959 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16144 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0959 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16145 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0959 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16148 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0959 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16149 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0959 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16151 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0959 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16152 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0242 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0959 at hbad
  cases hcolor0 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16153 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16154 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16155 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16156 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16157 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16158 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16159 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16160 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16161 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0960 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16162 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0960 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16164 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0960 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16168 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0960 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16169 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0960 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16171 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0960 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16173 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0960 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16175 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0960 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16176 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0960 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16177 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16178 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16179 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16180 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16181 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16182 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16183 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16184 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16185 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0961 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16186 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0961 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16188 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0961 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16189 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0961 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16192 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0961 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16193 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0961 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16197 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0961 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16199 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0961 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16200 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0961 at hbad
  cases hcolor0 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16201 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16202 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16203 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16204 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16205 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16206 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16207 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16208 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16209 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0962 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16210 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0962 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16212 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0962 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16217 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0962 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16219 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0962 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16220 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0962 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16221 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0962 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16224 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0244 PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0962 at hbad
  cases hcolor0 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16225 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16226 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16227 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16228 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16229 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16230 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16231 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16232 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16233 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16234 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16235 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16236 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16237 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16239 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16240 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16241 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16245 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16246 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16247 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16248 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0963 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16249 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16250 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16251 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16252 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16253 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16254 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16255 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16256 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16257 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16258 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16260 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16264 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16265 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16266 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16269 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16270 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16271 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16272 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0964 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16273 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16274 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16275 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16276 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16277 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16278 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16279 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16280 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16281 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0965 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16282 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0965 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16284 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0965 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16286 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0965 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16288 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0247 PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0965 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
