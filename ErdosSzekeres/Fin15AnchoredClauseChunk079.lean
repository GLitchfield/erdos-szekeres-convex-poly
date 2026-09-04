module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 079. -/

theorem fin15Anchored_clause10112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 Fin15AnchoredAtom1122 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 Fin15AnchoredAtom1123 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 Fin15AnchoredAtom1123 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10115 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 Fin15AnchoredAtom1123 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10116 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 Fin15AnchoredAtom1123 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 Fin15AnchoredAtom1123 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 Fin15AnchoredAtom1123 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 Fin15AnchoredAtom1123 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 Fin15AnchoredAtom1123 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10121 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10122 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10123 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 Fin15AnchoredAtom1124 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10131 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 Fin15AnchoredAtom1125 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10132 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 Fin15AnchoredAtom1125 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10133 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 Fin15AnchoredAtom1125 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10134 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 Fin15AnchoredAtom1125 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 Fin15AnchoredAtom1125 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 Fin15AnchoredAtom1125 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 Fin15AnchoredAtom1125 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 Fin15AnchoredAtom1125 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10139 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom1126 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 Fin15AnchoredAtom1126 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom1126 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 Fin15AnchoredAtom1126 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom1126 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 Fin15AnchoredAtom1126 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 Fin15AnchoredAtom1127 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 Fin15AnchoredAtom1127 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10144 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 Fin15AnchoredAtom1127 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10145 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 Fin15AnchoredAtom1127 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10146 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 Fin15AnchoredAtom1127 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 Fin15AnchoredAtom1127 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 Fin15AnchoredAtom1127 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 Fin15AnchoredAtom1127 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 Fin15AnchoredAtom1127 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10151 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 Fin15AnchoredAtom1128 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 Fin15AnchoredAtom1128 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 Fin15AnchoredAtom1128 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10154 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 Fin15AnchoredAtom1128 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 Fin15AnchoredAtom1128 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 Fin15AnchoredAtom1128 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 Fin15AnchoredAtom1128 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 Fin15AnchoredAtom1128 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 Fin15AnchoredAtom1128 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10160 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 Fin15AnchoredAtom1129 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 Fin15AnchoredAtom1129 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 Fin15AnchoredAtom1129 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 Fin15AnchoredAtom1129 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 Fin15AnchoredAtom1129 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 Fin15AnchoredAtom1129 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10166 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 Fin15AnchoredAtom1130 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10167 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 Fin15AnchoredAtom1130 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10168 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 Fin15AnchoredAtom1130 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10169 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 Fin15AnchoredAtom1130 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 Fin15AnchoredAtom1130 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 Fin15AnchoredAtom1130 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 Fin15AnchoredAtom1130 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 Fin15AnchoredAtom1130 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10174 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 Fin15AnchoredAtom1131 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10175 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 Fin15AnchoredAtom1131 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10176 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 Fin15AnchoredAtom1131 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10177 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 Fin15AnchoredAtom1131 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 Fin15AnchoredAtom1131 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 Fin15AnchoredAtom1131 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 Fin15AnchoredAtom1131 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 Fin15AnchoredAtom1131 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10182 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 Fin15AnchoredAtom1132 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10183 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 Fin15AnchoredAtom1132 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10184 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 Fin15AnchoredAtom1132 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10185 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 Fin15AnchoredAtom1132 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 Fin15AnchoredAtom1132 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 Fin15AnchoredAtom1132 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 Fin15AnchoredAtom1132 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 Fin15AnchoredAtom1132 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 Fin15AnchoredAtom1132 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10191 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom1133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 Fin15AnchoredAtom1133 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom1133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 Fin15AnchoredAtom1133 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom1133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 Fin15AnchoredAtom1133 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom1133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 Fin15AnchoredAtom1133 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10195 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 Fin15AnchoredAtom1134 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10196 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 Fin15AnchoredAtom1134 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10197 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 Fin15AnchoredAtom1134 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10198 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 Fin15AnchoredAtom1134 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10199 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 Fin15AnchoredAtom1134 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 Fin15AnchoredAtom1134 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 Fin15AnchoredAtom1134 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 Fin15AnchoredAtom1134 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 Fin15AnchoredAtom1134 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10204 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 Fin15AnchoredAtom1135 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10205 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 Fin15AnchoredAtom1135 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10206 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 Fin15AnchoredAtom1135 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10207 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 Fin15AnchoredAtom1135 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 Fin15AnchoredAtom1135 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 Fin15AnchoredAtom1135 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 Fin15AnchoredAtom1135 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 Fin15AnchoredAtom1135 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10212 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 Fin15AnchoredAtom1136 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10213 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 Fin15AnchoredAtom1136 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10214 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 Fin15AnchoredAtom1136 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 Fin15AnchoredAtom1136 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 Fin15AnchoredAtom1136 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 Fin15AnchoredAtom1136 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 Fin15AnchoredAtom1136 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10219 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 Fin15AnchoredAtom1137 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10220 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 Fin15AnchoredAtom1137 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10221 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 Fin15AnchoredAtom1137 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10222 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 Fin15AnchoredAtom1137 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 Fin15AnchoredAtom1137 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 Fin15AnchoredAtom1137 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 Fin15AnchoredAtom1137 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 Fin15AnchoredAtom1137 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10227 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 Fin15AnchoredAtom1138 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10228 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 Fin15AnchoredAtom1138 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 Fin15AnchoredAtom1138 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10230 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 Fin15AnchoredAtom1138 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 Fin15AnchoredAtom1138 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 Fin15AnchoredAtom1138 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 Fin15AnchoredAtom1138 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 Fin15AnchoredAtom1138 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10235 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 Fin15AnchoredAtom1139 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10236 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 Fin15AnchoredAtom1139 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 Fin15AnchoredAtom1139 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 Fin15AnchoredAtom1139 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 Fin15AnchoredAtom1139 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
