module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 094. -/

theorem fin15Anchored_clause12032 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0252 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1398 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12033 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
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

theorem fin15Anchored_clause12034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0252 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1398 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
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

theorem fin15Anchored_clause12036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0252 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1398 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0252 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0363 Fin15AnchoredAtom1398 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12038 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0253 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1399 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12039 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0253 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1399 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12040 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0253 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1399 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12041 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0253 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1399 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0253 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1399 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0253 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1399 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0253 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1399 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0253 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1399 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0253 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0364 Fin15AnchoredAtom1399 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12047 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0254 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1400 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12048 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0254 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1400 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12049 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0254 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1400 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12050 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0254 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1400 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0254 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1400 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0254 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1400 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0254 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1400 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0254 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1400 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0250 Fin15AnchoredAtom0254 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0365 Fin15AnchoredAtom1400 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12056 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0252 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1401 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12057 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0252 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1401 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12058 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0252 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1401 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12059 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0252 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1401 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12060 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0252 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1401 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0252 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1401 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0252 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0366 Fin15AnchoredAtom1401 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12063 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0253 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0367 Fin15AnchoredAtom1402 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12064 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom1402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0253 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0367 Fin15AnchoredAtom1402 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12065 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom1403 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0254 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0368 Fin15AnchoredAtom1403 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12066 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom1403 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0254 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0368 Fin15AnchoredAtom1403 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12067 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom1403 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0251 Fin15AnchoredAtom0254 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0368 Fin15AnchoredAtom1403 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12068 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0253 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1404 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12069 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0253 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1404 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12070 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0253 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1404 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12071 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0253 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1404 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0253 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1404 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0253 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1404 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0253 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1404 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0253 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0369 Fin15AnchoredAtom1404 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12076 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12077 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12078 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12079 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0252 Fin15AnchoredAtom0254 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0370 Fin15AnchoredAtom1405 at hbad
  cases hcolor0 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12086 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1406 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12087 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1406 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12088 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1406 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12089 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1406 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1406 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1406 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1406 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1406 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0253 Fin15AnchoredAtom0254 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0371 Fin15AnchoredAtom1406 at hbad
  cases hcolor0 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12095 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1407 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12096 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1407 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12097 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1407 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12098 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1407 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1407 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1407 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0256 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0372 Fin15AnchoredAtom1407 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12103 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12104 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12105 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0257 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0373 Fin15AnchoredAtom1408 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12112 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1409 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1409 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1409 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12115 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1409 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1409 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1409 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1409 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0258 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0374 Fin15AnchoredAtom1409 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12120 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0259 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1410 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0259 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0375 Fin15AnchoredAtom1410 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12122 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12123 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12126 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0260 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0376 Fin15AnchoredAtom1411 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12132 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1412 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12133 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1412 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12134 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1412 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12135 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1412 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1412 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1412 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1412 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1412 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0261 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0377 Fin15AnchoredAtom1412 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12141 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1413 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1413 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1413 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12144 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1413 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1413 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1413 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1413 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1413 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0255 Fin15AnchoredAtom0262 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0378 Fin15AnchoredAtom1413 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12150 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12151 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12154 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0256 Fin15AnchoredAtom0257 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0379 Fin15AnchoredAtom1414 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
