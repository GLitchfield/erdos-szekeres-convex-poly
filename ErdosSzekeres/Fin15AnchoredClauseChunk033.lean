module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 033. -/

theorem fin15Anchored_clause04224 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04225 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04226 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04227 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04228 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04229 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04230 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04231 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04232 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04233 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04234 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04235 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04236 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04237 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04238 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04239 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04240 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04241 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04242 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04243 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04244 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04245 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04246 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04247 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04248 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04249 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04250 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04251 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04252 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04253 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04254 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04255 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04256 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04257 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04258 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04259 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04260 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0259 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04261 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0259 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04262 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0259 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04263 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0259 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04264 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0259 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04265 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04266 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04267 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04268 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04269 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04270 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04271 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04272 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04273 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04274 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04275 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04276 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04277 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04278 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04279 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04280 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04281 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04282 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04283 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04284 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04285 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04286 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04287 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04288 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04289 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04290 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04291 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04292 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04293 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04294 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04295 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04296 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04297 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04298 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04299 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04300 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04301 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04302 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04303 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04304 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0258 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04305 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04306 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04307 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04308 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04309 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04310 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04311 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04312 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0260 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04313 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04314 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04315 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04316 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04317 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04318 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04319 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04320 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0261 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04321 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04322 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04323 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04324 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04325 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04326 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04327 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04328 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0262 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04329 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04330 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04331 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04332 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04333 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04334 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04335 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04336 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0258 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04337 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04338 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04339 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04340 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04341 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04342 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04343 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04344 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0259 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04345 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04346 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04347 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04348 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04349 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04350 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04351 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0257 Fin15AnchoredAtom0260 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
