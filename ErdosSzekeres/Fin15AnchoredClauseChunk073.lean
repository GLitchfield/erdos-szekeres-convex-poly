module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 073. -/

theorem fin15Anchored_clause09344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0132 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1019 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09346 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1020 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09347 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1020 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09348 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1020 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09349 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1020 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1020 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1020 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1020 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1020 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0131 Fin15AnchoredAtom0133 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1020 at hbad
  cases hcolor0 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09355 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09356 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09357 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09358 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09359 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09363 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0132 Fin15AnchoredAtom0133 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1021 at hbad
  cases hcolor0 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09365 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1022 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09366 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1022 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09367 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1022 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09368 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1022 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1022 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1022 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0135 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1022 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09372 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1023 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1023 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09374 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1023 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09375 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1023 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1023 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1023 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1023 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0136 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1023 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09381 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09382 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09383 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09384 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09385 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0137 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1024 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09391 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1025 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0138 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1025 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09392 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1026 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09393 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1026 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09394 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1026 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09395 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1026 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1026 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1026 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1026 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0139 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1026 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09400 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09401 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09402 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09403 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09404 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0140 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1027 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09410 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09411 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09412 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09413 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0134 Fin15AnchoredAtom0141 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1028 at hbad
  cases hcolor0 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09421 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1029 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09422 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1029 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09423 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1029 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09424 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1029 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1029 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1029 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1029 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1029 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0136 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1029 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09430 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1030 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09431 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1030 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09432 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1030 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09433 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1030 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09434 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1030 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1030 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1030 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1030 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0137 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1030 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09439 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1032 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09440 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1032 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09441 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1032 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09442 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1032 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1032 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1032 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1032 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1032 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0139 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1032 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09448 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09449 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09451 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09452 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09453 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0140 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1033 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09458 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09459 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09460 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09461 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09463 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0135 Fin15AnchoredAtom0141 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0384 Fin15AnchoredAtom1034 at hbad
  cases hcolor0 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09469 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09470 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09471 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0136 Fin15AnchoredAtom0137 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1035 at hbad
  cases hcolor0 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
