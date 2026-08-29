module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 031. -/

theorem predecessorHalfFin13_clause11849 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0154 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0154 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0780 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11853 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0154 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0780 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11855 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0154 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0780 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11856 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0154 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0154 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0780 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11857 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11858 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11859 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11860 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11862 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11863 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11864 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11865 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0781 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11867 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0781 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11868 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0155 chi ∧
      ¬PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0781 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11872 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0781 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11877 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0781 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11879 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0781 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11880 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0155 chi ∧
      PredecessorHalfFin13Atom0156 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0155 PredecessorHalfFin13Atom0156 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0781 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11881 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11882 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11883 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11884 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11885 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11886 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11887 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11888 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11889 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0782 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11890 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0782 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11892 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0782 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11894 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0782 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11896 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0782 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11897 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0782 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11901 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0782 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11903 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0782 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11904 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0782 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11905 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11906 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11907 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11908 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11909 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11910 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11911 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11912 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11913 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0783 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11914 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0783 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11916 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0783 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11920 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0783 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11921 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0783 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11925 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0783 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11927 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0783 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11928 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0783 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11929 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11930 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11931 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11932 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11933 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11934 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11935 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11936 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11937 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11938 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11940 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11942 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11944 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11945 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11948 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11949 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11951 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11952 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0157 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0157 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0784 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11953 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11954 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11955 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11956 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11957 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11958 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11959 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11960 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11961 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11962 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11963 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11964 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11966 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11968 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11969 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11973 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11975 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11976 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0785 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11977 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11978 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11979 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11980 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11981 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11982 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11983 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11984 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11985 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11986 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11987 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11988 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11990 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11992 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11993 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11997 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause11999 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12000 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0158 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0786 at hbad
  cases hcolor0 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12001 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12002 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12003 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12004 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12005 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12006 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12008 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12009 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0787 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12010 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0787 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12017 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0787 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12019 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0787 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12021 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0787 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12023 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0787 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12024 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0159 PredecessorHalfFin13Atom0160 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0787 at hbad
  cases hcolor0 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12025 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12026 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12027 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12028 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12029 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12030 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12031 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12032 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12033 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
