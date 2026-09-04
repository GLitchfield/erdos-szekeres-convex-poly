module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 113. -/

theorem fin15Anchored_clause14464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0373 Fin15AnchoredAtom0379
    Fin15AnchoredAtom0400 Fin15AnchoredAtom1695 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14468 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1696 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14469 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1696 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14470 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1696 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14471 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1696 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1696 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1696 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1696 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0374 Fin15AnchoredAtom0380
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1696 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14476 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1698 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14477 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1698 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14478 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1698 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14479 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1698 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1698 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1698 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1698 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1698 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0376 Fin15AnchoredAtom0382
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1698 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14485 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14487 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14488 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14489 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14490 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14491 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0377 Fin15AnchoredAtom0383
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1699 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14497 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14498 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14499 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14500 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14501 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14502 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0372 Fin15AnchoredAtom0378 Fin15AnchoredAtom0384
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1700 at hbad
  cases hcolor0 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14509 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14510 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14511 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14512 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14513 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0374 Fin15AnchoredAtom0385
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1701 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14519 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1702 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14520 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1702 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1702 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1702 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1702 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0375 Fin15AnchoredAtom0386
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1702 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14525 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14526 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14527 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14528 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14529 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14530 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0376 Fin15AnchoredAtom0387
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1703 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14537 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14538 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14539 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14540 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14541 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14542 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0377 Fin15AnchoredAtom0388
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1704 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14549 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14550 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14551 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14553 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0373 Fin15AnchoredAtom0378 Fin15AnchoredAtom0389
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1705 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14560 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14561 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14562 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14563 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14564 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14565 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0375 Fin15AnchoredAtom0390
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1706 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14571 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14572 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14573 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14574 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14575 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14576 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0376 Fin15AnchoredAtom0391
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1707 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14582 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14583 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14585 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14586 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause14591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0374 Fin15AnchoredAtom0377 Fin15AnchoredAtom0392
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1708 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
