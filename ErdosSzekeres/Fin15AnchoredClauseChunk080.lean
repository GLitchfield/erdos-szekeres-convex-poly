module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 080. -/

theorem fin15Anchored_clause10240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
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

theorem fin15Anchored_clause10241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
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

theorem fin15Anchored_clause10242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
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

theorem fin15Anchored_clause10243 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom1140 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0175 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0270 Fin15AnchoredAtom1140 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom1140 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0175 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0270 Fin15AnchoredAtom1140 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10245 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom1141 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0176 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0271 Fin15AnchoredAtom1141 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10246 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom1141 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0176 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0271 Fin15AnchoredAtom1141 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10247 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom1143 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0178 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0273 Fin15AnchoredAtom1143 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10248 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom1143 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0178 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0273 Fin15AnchoredAtom1143 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom1144 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0179 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0274 Fin15AnchoredAtom1144 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom1145 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0180 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0275 Fin15AnchoredAtom1145 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10251 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 Fin15AnchoredAtom1146 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10252 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 Fin15AnchoredAtom1146 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 Fin15AnchoredAtom1146 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10254 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 Fin15AnchoredAtom1146 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 Fin15AnchoredAtom1146 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 Fin15AnchoredAtom1146 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 Fin15AnchoredAtom1146 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 Fin15AnchoredAtom1146 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 Fin15AnchoredAtom1146 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10260 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom1147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 Fin15AnchoredAtom1147 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom1147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 Fin15AnchoredAtom1147 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom1147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 Fin15AnchoredAtom1147 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom1147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 Fin15AnchoredAtom1147 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom1147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 Fin15AnchoredAtom1147 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10265 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 Fin15AnchoredAtom1148 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10266 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 Fin15AnchoredAtom1148 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10267 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 Fin15AnchoredAtom1148 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10268 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 Fin15AnchoredAtom1148 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 Fin15AnchoredAtom1148 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 Fin15AnchoredAtom1148 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 Fin15AnchoredAtom1148 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 Fin15AnchoredAtom1148 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10273 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 Fin15AnchoredAtom1149 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10274 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 Fin15AnchoredAtom1149 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10275 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 Fin15AnchoredAtom1149 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 Fin15AnchoredAtom1149 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 Fin15AnchoredAtom1149 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 Fin15AnchoredAtom1149 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 Fin15AnchoredAtom1149 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 Fin15AnchoredAtom1149 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10281 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 Fin15AnchoredAtom1150 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10282 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 Fin15AnchoredAtom1150 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 Fin15AnchoredAtom1150 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10284 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 Fin15AnchoredAtom1150 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10285 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 Fin15AnchoredAtom1150 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 Fin15AnchoredAtom1150 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 Fin15AnchoredAtom1150 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 Fin15AnchoredAtom1150 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 Fin15AnchoredAtom1150 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 Fin15AnchoredAtom1151 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 Fin15AnchoredAtom1151 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 Fin15AnchoredAtom1151 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 Fin15AnchoredAtom1151 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 Fin15AnchoredAtom1151 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 Fin15AnchoredAtom1151 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10296 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 Fin15AnchoredAtom1152 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10297 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 Fin15AnchoredAtom1152 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10298 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 Fin15AnchoredAtom1152 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10299 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 Fin15AnchoredAtom1152 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 Fin15AnchoredAtom1152 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 Fin15AnchoredAtom1152 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 Fin15AnchoredAtom1152 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 Fin15AnchoredAtom1152 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10304 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 Fin15AnchoredAtom1153 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10305 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 Fin15AnchoredAtom1153 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10306 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 Fin15AnchoredAtom1153 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10307 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 Fin15AnchoredAtom1153 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 Fin15AnchoredAtom1153 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 Fin15AnchoredAtom1153 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 Fin15AnchoredAtom1153 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 Fin15AnchoredAtom1153 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0179 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0283 Fin15AnchoredAtom1153 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 Fin15AnchoredAtom1154 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10314 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 Fin15AnchoredAtom1154 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 Fin15AnchoredAtom1154 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10316 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 Fin15AnchoredAtom1154 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 Fin15AnchoredAtom1154 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 Fin15AnchoredAtom1154 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 Fin15AnchoredAtom1154 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 Fin15AnchoredAtom1154 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0180 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0284 Fin15AnchoredAtom1154 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10322 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom1155 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 Fin15AnchoredAtom1155 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10323 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom1155 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 Fin15AnchoredAtom1155 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10324 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom1155 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 Fin15AnchoredAtom1155 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom1155 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 Fin15AnchoredAtom1155 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom1155 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0178 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0285 Fin15AnchoredAtom1155 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10327 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 Fin15AnchoredAtom1156 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10328 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 Fin15AnchoredAtom1156 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 Fin15AnchoredAtom1156 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 Fin15AnchoredAtom1156 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 Fin15AnchoredAtom1156 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0179 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0286 Fin15AnchoredAtom1156 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10333 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom1157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0180 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0287 Fin15AnchoredAtom1157 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom1157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0180 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0287 Fin15AnchoredAtom1157 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10335 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom1157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0180 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0287 Fin15AnchoredAtom1157 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom1157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0177 Fin15AnchoredAtom0180 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0287 Fin15AnchoredAtom1157 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10337 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 Fin15AnchoredAtom1158 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10338 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 Fin15AnchoredAtom1158 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10339 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 Fin15AnchoredAtom1158 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10340 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 Fin15AnchoredAtom1158 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 Fin15AnchoredAtom1158 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 Fin15AnchoredAtom1158 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 Fin15AnchoredAtom1158 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 Fin15AnchoredAtom1158 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0179 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0288 Fin15AnchoredAtom1158 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10346 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10347 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10348 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10349 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10350 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0178 Fin15AnchoredAtom0180 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0289 Fin15AnchoredAtom1159 at hbad
  cases hcolor0 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10356 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 Fin15AnchoredAtom1160 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10357 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 Fin15AnchoredAtom1160 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10358 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 Fin15AnchoredAtom1160 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10359 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 Fin15AnchoredAtom1160 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10360 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 Fin15AnchoredAtom1160 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 Fin15AnchoredAtom1160 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 Fin15AnchoredAtom1160 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10363 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 Fin15AnchoredAtom1160 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0179 Fin15AnchoredAtom0180 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0290 Fin15AnchoredAtom1160 at hbad
  cases hcolor0 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10365 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1161 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10366 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1161 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10367 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0181 Fin15AnchoredAtom0182 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0291 Fin15AnchoredAtom1161 at hbad
  cases hcolor0 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
