module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 097. -/

theorem fin15Anchored_clause12416 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12417 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0267 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1447 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12424 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12425 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12426 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12427 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12428 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0268 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1448 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12434 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12435 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12436 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12437 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12438 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12439 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0265 Fin15AnchoredAtom0269 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1449 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12445 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1450 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0267 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1450 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1450 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0267 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1450 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1450 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0267 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1450 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1450 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0267 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1450 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12449 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0269 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1452 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0269 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1452 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12451 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0266 Fin15AnchoredAtom0269 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1452 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12452 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12453 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12454 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12455 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12456 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0268 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1453 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12463 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12464 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12465 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12466 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0267 Fin15AnchoredAtom0269 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1454 at hbad
  cases hcolor0 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12472 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12473 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12474 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12475 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12476 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0268 Fin15AnchoredAtom0269 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1455 at hbad
  cases hcolor0 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12483 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12485 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12487 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0271 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1456 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12493 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12494 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12495 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12496 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12497 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0273 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1458 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12503 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1459 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12504 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1459 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12505 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1459 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12506 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1459 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1459 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1459 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1459 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1459 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0274 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1459 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12512 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12513 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12514 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12515 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0270 Fin15AnchoredAtom0275 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1460 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12521 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1462 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12522 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1462 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12523 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1462 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12524 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1462 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1462 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1462 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1462 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0273 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1462 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12529 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12530 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12531 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12532 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12533 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0274 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1463 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12540 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1464 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12541 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1464 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12542 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1464 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12543 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1464 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
