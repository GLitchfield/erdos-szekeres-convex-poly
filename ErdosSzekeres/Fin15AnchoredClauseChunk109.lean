module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 109. -/

theorem fin15Anchored_clause13952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 Fin15AnchoredAtom1631 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13953 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13954 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13955 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13956 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13957 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13958 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 Fin15AnchoredAtom1632 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13963 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1633 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13964 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1633 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13965 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1633 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1633 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1633 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 Fin15AnchoredAtom1633 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13969 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1634 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom1634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 Fin15AnchoredAtom1634 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13971 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom1635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0343 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0396 Fin15AnchoredAtom1635 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13972 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13973 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13974 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13975 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13976 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13977 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13979 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 Fin15AnchoredAtom1636 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13985 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1637 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13986 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1637 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13987 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1637 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1637 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1637 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1637 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1637 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1637 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 Fin15AnchoredAtom1637 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1638 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13995 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1638 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13996 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1638 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13997 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1638 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1638 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1638 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1638 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0342 Fin15AnchoredAtom0343 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0399 Fin15AnchoredAtom1638 at hbad
  cases hcolor0 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14002 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14003 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14004 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14005 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14006 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0345 Fin15AnchoredAtom0351
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1639 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1640 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14014 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1640 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14015 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1640 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14016 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1640 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1640 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1640 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1640 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1640 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0346 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1640 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14022 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14023 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14024 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14025 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14026 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0348 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1642 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14033 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14034 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14035 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14036 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14037 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0349 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1643 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14043 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1644 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14044 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1644 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14045 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1644 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14046 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1644 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14047 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1644 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1644 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1644 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1644 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0344 Fin15AnchoredAtom0350 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1644 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14052 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1645 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14053 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1645 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14054 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1645 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14055 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1645 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14056 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1645 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1645 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1645 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1645 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0346 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1645 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14061 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1646 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14062 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1646 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14063 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1646 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14064 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1646 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1646 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1646 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1646 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1646 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0347 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1646 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14070 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14071 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14072 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14073 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14074 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14075 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0345 Fin15AnchoredAtom0348 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1647 at hbad
  cases hcolor0 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
