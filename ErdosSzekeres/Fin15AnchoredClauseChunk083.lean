module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 083. -/

theorem fin15Anchored_clause10624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1196 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 Fin15AnchoredAtom1196 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom1196 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 Fin15AnchoredAtom1196 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1196 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 Fin15AnchoredAtom1196 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10627 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1197 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10628 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1197 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10629 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1197 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1197 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1197 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1197 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1197 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1197 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10635 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1198 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10636 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1198 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10637 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1198 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10638 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1198 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1198 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1198 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1198 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1198 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1198 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10644 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1199 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10645 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1199 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10646 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1199 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10647 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1199 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1199 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1199 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1199 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1199 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1199 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10653 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 Fin15AnchoredAtom1200 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 Fin15AnchoredAtom1200 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom1200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 Fin15AnchoredAtom1200 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10656 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom1201 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0189 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0331 Fin15AnchoredAtom1201 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom1201 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0189 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0331 Fin15AnchoredAtom1201 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom1201 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0189 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0331 Fin15AnchoredAtom1201 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10659 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1203 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10660 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1203 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10661 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1203 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10662 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1203 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1203 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1203 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1203 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1203 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10667 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1204 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10668 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1204 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10669 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1204 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10670 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1204 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1204 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1204 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1204 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1204 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10675 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1205 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10676 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1205 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10677 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1205 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10678 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1205 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10679 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1205 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1205 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1205 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10682 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1205 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 Fin15AnchoredAtom1205 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10684 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1206 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10685 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1206 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10686 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1206 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10687 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1206 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1206 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1206 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1206 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1206 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0192 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1206 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1207 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0193 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1207 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1207 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0193 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1207 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1207 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0193 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1207 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10696 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1208 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10697 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1208 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10698 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1208 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1208 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1208 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1208 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1208 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1208 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0194 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1208 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10705 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1209 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10706 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1209 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1209 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10708 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1209 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1209 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1209 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1209 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0195 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1209 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10713 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1210 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10714 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1210 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10715 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1210 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1210 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1210 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1210 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0196 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1210 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10720 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10721 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10722 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10723 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10724 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0197 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1211 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10730 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1212 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1212 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10732 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1212 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10733 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1212 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1212 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1212 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10736 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1212 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1212 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0198 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1212 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10739 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10740 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10741 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10743 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0191 Fin15AnchoredAtom0199 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1213 at hbad
  cases hcolor0 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1214 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10750 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1214 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10751 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0193 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1214 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
