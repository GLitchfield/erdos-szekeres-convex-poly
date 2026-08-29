module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 051. -/

theorem predecessorHalfFin13_clause15393 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0928 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15394 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0928 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15396 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0928 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15399 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0928 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15400 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0928 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15401 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0928 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15405 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0928 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15407 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0928 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15408 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0928 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15409 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15410 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15411 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15412 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15413 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15414 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15415 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15416 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15417 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15418 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15419 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15420 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15424 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15425 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15428 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15429 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15431 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15432 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0225 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0929 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15433 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15434 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15435 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15436 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15437 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15438 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15439 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15440 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15441 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15442 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15444 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15448 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15449 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15450 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15451 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15452 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15453 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15455 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15456 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0226 PredecessorHalfFin13Atom0227 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0930 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15457 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15458 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15459 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15460 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15461 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15462 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15463 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15464 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15465 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0931 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15466 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0931 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15468 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0931 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15470 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0931 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15472 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0931 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15473 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0931 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15477 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0931 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15479 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0931 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15480 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0230 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0228 PredecessorHalfFin13Atom0229 PredecessorHalfFin13Atom0230
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0931 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15481 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15482 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15483 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15484 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15485 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15486 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15487 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15488 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15489 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15490 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15491 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15492 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15496 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15497 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15499 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15500 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15501 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15503 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15504 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0237
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0932 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15505 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15506 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15507 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15508 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15509 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15510 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15511 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15512 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15513 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0933 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15514 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0933 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15516 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0933 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15520 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0933 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15521 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0933 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15522 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0933 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15525 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0933 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15527 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0933 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15528 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0238
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0933 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15529 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15530 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15531 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15532 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15533 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15534 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15535 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15536 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15537 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15538 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15540 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15544 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15545 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15546 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15549 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15550 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15551 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15552 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0239
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0934 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15553 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15554 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15555 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15556 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15557 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15558 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15559 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15560 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15561 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0935 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15562 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0935 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15568 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0935 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
