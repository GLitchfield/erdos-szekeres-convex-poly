module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 085. -/

theorem fin15Anchored_clause10880 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0199 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1235 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
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

theorem fin15Anchored_clause10882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0199 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1235 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
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

theorem fin15Anchored_clause10884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0199 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1235 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0195 Fin15AnchoredAtom0199 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1235 at hbad
  cases hcolor0 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10886 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1236 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0196 Fin15AnchoredAtom0197 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1236 at hbad
  cases hcolor0 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1236 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0196 Fin15AnchoredAtom0197 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1236 at hbad
  cases hcolor0 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1236 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0196 Fin15AnchoredAtom0197 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1236 at hbad
  cases hcolor0 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10889 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1237 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0196 Fin15AnchoredAtom0198 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0367 Fin15AnchoredAtom1237 at hbad
  cases hcolor0 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10890 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1237 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0196 Fin15AnchoredAtom0198 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0367 Fin15AnchoredAtom1237 at hbad
  cases hcolor0 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom1238 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0196 Fin15AnchoredAtom0199 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0368 Fin15AnchoredAtom1238 at hbad
  cases hcolor0 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10892 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10893 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10894 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10895 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10896 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0198 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1239 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10902 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0199 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1240 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10903 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0199 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1240 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10904 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0199 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1240 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10905 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0199 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1240 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0199 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1240 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0199 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1240 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0199 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1240 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0197 Fin15AnchoredAtom0199 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1240 at hbad
  cases hcolor0 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10910 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1241 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10911 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1241 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10912 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1241 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10913 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1241 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1241 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1241 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1241 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1241 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10918 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1242 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10919 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1242 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10920 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1242 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1242 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1242 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10923 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1243 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10924 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1243 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10925 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1243 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10926 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1243 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10927 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1243 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1243 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1243 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1243 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1243 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10932 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1244 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10933 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1244 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10934 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1244 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1244 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1244 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1244 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1244 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1244 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10940 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1245 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10941 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1245 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10942 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1245 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10943 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1245 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10944 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1245 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1245 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1245 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10947 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10948 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10949 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10950 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10951 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1246 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10957 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10958 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10959 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10960 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10961 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10962 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1247 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10968 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1248 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10969 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1248 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10970 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1248 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10971 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1248 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1248 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1248 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1248 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1248 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1248 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10977 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1249 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1249 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1249 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1249 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10981 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1250 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10982 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1250 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10983 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1250 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10984 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1250 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1250 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1250 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 Fin15AnchoredAtom1250 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1252 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0205 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1252 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1252 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0205 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0382 Fin15AnchoredAtom1252 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1253 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0206 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0383 Fin15AnchoredAtom1253 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10991 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1255 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10992 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1255 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10993 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1255 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1255 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1255 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1255 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1255 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1255 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause10999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 Fin15AnchoredAtom1255 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11000 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1256 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11001 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1256 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11002 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1256 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11003 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1256 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1256 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1256 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1256 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 Fin15AnchoredAtom1256 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
