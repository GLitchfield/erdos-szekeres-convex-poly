module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 093. -/

theorem fin15Anchored_clause11904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1383 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11909 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11910 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11911 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11912 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11913 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1384 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11919 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1385 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11920 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1385 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11921 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1385 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11922 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1385 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1385 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1385 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1385 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1385 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1385 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11928 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11929 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11930 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11931 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11932 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11933 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1386 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11938 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1387 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11939 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1387 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11940 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1387 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11941 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1387 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11942 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1387 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1387 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1387 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1387 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1387 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11947 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0252 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1389 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11948 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0252 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1389 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11949 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0252 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1389 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11950 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0252 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1389 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0252 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1389 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0252 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1389 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0252 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1389 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0252 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1389 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0252 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1389 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11956 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11957 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11958 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11959 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11960 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11961 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0253 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1390 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11967 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0254 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1391 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11968 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0254 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1391 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11969 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0254 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1391 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11970 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0254 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1391 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0254 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1391 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0254 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1391 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0254 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1391 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0254 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1391 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11975 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11976 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11977 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0250 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0357 Fin15AnchoredAtom1392 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11986 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0251 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1393 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11987 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0251 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1393 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0251 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1393 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11989 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0251 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1393 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0251 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1393 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0251 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1393 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0251 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1393 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0251 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0358 Fin15AnchoredAtom1393 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0252 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1394 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11995 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0252 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1394 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11996 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0252 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1394 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11997 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0252 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1394 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0252 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1394 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0252 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1394 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0252 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1394 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0252 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0359 Fin15AnchoredAtom1394 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12002 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0253 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1395 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12003 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0253 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1395 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12004 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0253 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1395 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12005 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0253 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1395 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0253 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1395 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0253 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1395 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0253 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1395 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0253 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1395 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0253 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0360 Fin15AnchoredAtom1395 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12011 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12012 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12014 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12015 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0249 Fin15AnchoredAtom0254 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0361 Fin15AnchoredAtom1396 at hbad
  cases hcolor0 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12022 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0251 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1397 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12023 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0251 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1397 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12024 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0251 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1397 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12025 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0251 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1397 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12026 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0251 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1397 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0251 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1397 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0251 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1397 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0251 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0362 Fin15AnchoredAtom1397 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12030 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0252 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1398 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12031 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0252 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1398 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
