module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 082. -/

theorem fin15Anchored_clause10496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0189 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0306 Fin15AnchoredAtom1176 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10500 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1177 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10501 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1177 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10502 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1177 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10503 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1177 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1177 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1177 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1177 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0182 Fin15AnchoredAtom0190 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0307 Fin15AnchoredAtom1177 at hbad
  cases hcolor0 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10508 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1178 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10509 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1178 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1178 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1178 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom1178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1178 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom1178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0184 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0308 Fin15AnchoredAtom1178 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10514 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1179 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10515 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1179 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10516 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1179 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10517 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1179 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1179 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1179 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1179 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1179 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0185 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0309 Fin15AnchoredAtom1179 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10523 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10524 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10525 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10526 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0186 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0310 Fin15AnchoredAtom1180 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10533 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 Fin15AnchoredAtom1181 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10534 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 Fin15AnchoredAtom1181 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10535 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom1181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 Fin15AnchoredAtom1181 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom1181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 Fin15AnchoredAtom1181 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom1181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0187 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0311 Fin15AnchoredAtom1181 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10538 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1182 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10539 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1182 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10540 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1182 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10541 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1182 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1182 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1182 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1182 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1182 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0188 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0312 Fin15AnchoredAtom1182 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10547 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1183 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10548 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1183 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10549 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1183 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10550 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1183 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1183 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1183 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1183 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1183 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0189 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0313 Fin15AnchoredAtom1183 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10556 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1184 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10557 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1184 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1184 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10559 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1184 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10560 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1184 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1184 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1184 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1184 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0183 Fin15AnchoredAtom0190 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0314 Fin15AnchoredAtom1184 at hbad
  cases hcolor0 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10565 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1185 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10566 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1185 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10567 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom1185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1185 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1185 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom1185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0185 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0315 Fin15AnchoredAtom1185 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10570 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1186 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1186 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10571 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1186 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1186 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1186 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1186 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10573 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1188 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10574 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1188 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10575 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1188 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1188 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1188 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1188 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1189 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0189 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0319 Fin15AnchoredAtom1189 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10580 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1190 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10581 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1190 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1190 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10583 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1191 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1191 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10585 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1191 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10586 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1191 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1191 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1191 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1191 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1191 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1191 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10592 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1192 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10593 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1192 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1192 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1192 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1193 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10597 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1193 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10598 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1193 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10599 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1193 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1193 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1193 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1193 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1193 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1194 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10605 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1194 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1194 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1194 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10608 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1194 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1194 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1194 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1194 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1194 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10613 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1195 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10614 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1195 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10615 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1195 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10616 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1195 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1195 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1195 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1195 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1195 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1195 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10622 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
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

theorem fin15Anchored_clause10623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
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

end ErdosSzekeres

end
