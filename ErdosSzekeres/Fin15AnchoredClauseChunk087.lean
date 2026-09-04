module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 087. -/

theorem fin15Anchored_clause11136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11137 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11138 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11139 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1276 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11145 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1277 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11146 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1277 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1277 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1277 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1277 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1277 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1277 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1278 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1278 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11154 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1278 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11155 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1278 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11156 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1278 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1278 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1278 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1278 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1278 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11162 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11163 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11164 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11165 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11166 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1279 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11171 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1280 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1280 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11173 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1280 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11174 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1280 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1280 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1280 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1280 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1280 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0214 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1280 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11180 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11181 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11182 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11183 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11184 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11185 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0211 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1281 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11190 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1282 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11191 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1282 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11192 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1282 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11193 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1282 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1282 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1282 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1282 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1282 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0212 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1282 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11199 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11200 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11201 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11202 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11203 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0213 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1283 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11209 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11210 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11211 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11212 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11213 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11214 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0210 Fin15AnchoredAtom0214 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1284 at hbad
  cases hcolor0 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11219 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1285 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11220 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1285 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11221 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1285 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1285 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1285 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1285 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1285 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0212 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1285 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11227 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1286 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0213 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1286 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1286 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0213 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1286 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0214 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1287 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11230 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0214 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1287 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0214 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1287 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0211 Fin15AnchoredAtom0214 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1287 at hbad
  cases hcolor0 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11233 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11234 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11235 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11236 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0213 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1288 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11243 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1289 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1289 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11245 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1289 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11246 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1289 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1289 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1289 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1289 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0212 Fin15AnchoredAtom0214 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1289 at hbad
  cases hcolor0 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11251 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11252 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11254 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0213 Fin15AnchoredAtom0214 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1290 at hbad
  cases hcolor0 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11261 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1291 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1291 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0215 Fin15AnchoredAtom0216 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1291 at hbad
  cases hcolor0 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
