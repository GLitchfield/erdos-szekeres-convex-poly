module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 084. -/

theorem fin15Anchored_clause10752 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1215 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10753 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1215 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10754 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1215 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10755 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1215 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1215 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1215 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1215 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0194 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1215 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10760 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10761 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10762 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10763 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10764 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0195 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1216 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10770 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1217 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10771 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1217 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1217 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1217 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0196 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1217 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10775 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1218 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10776 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1218 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1218 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10778 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1218 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1218 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1218 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1218 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1218 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0197 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1218 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10784 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10785 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10786 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10787 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10789 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0198 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1219 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10795 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10796 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10797 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10798 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10799 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0192 Fin15AnchoredAtom0199 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1220 at hbad
  cases hcolor0 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10805 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1221 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0194 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1221 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1221 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0194 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1221 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10807 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0195 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1222 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10808 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0195 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1222 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10809 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0195 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1222 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10810 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0195 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1222 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0195 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1222 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0195 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1222 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0195 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1222 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10814 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1226 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0193 Fin15AnchoredAtom0199 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1226 at hbad
  cases hcolor0 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10815 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0195 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1227 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10816 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0195 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1227 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10817 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0195 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1227 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10818 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0195 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1227 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0195 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1227 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0195 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1227 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0195 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1227 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0195 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1227 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0195 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1227 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10824 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1228 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0196 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1228 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1228 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0196 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1228 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1228 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0196 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1228 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1228 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0196 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1228 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1228 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0196 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1228 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10829 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0197 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1229 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0197 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1229 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10831 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0197 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1229 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10832 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0197 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1229 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0197 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1229 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0197 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1229 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0197 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1229 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0197 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1229 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0197 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1229 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10838 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0198 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1230 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10839 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0198 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1230 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0198 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1230 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0198 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1230 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0198 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1230 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0198 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1230 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0198 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1230 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0198 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1230 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0198 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1230 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10847 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0199 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1231 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10848 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0199 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1231 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10849 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0199 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1231 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10850 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0199 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1231 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0199 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1231 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0199 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1231 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0199 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1231 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0194 Fin15AnchoredAtom0199 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1231 at hbad
  cases hcolor0 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10855 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0196 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1232 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10856 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0196 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1232 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10857 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0196 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1232 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0196 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1232 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0196 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1232 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0196 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1232 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0196 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1232 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10862 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0197 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1233 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10863 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0197 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1233 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10864 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0197 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1233 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10865 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0197 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1233 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0197 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1233 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0197 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1233 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0197 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1233 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0197 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1233 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10870 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0198 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1234 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10871 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0198 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1234 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10872 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0198 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1234 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10873 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0198 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1234 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0198 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1234 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0198 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1234 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0198 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1234 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0198 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1234 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0199 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1235 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10879 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0199 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1235 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
