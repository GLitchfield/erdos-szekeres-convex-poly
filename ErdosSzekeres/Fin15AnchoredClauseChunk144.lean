module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 144. -/

theorem fin15Anchored_clause18432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom2434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20553
  ] at hbad
  tauto

theorem fin15Anchored_clause18433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20553
  ] at hbad
  tauto

theorem fin15Anchored_clause18434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20553
  ] at hbad
  tauto

theorem fin15Anchored_clause18435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom2434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20553
  ] at hbad
  tauto

theorem fin15Anchored_clause18436 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom0626 Fin15AnchoredAtom0653
    Fin15AnchoredAtom0762 Fin15AnchoredAtom1433 Fin15AnchoredAtom2434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20553
  ] at hbad
  tauto

theorem fin15Anchored_clause18437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24649
  ] at hbad
  tauto

theorem fin15Anchored_clause18438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom2435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24649
  ] at hbad
  tauto

theorem fin15Anchored_clause18439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24649
  ] at hbad
  tauto

theorem fin15Anchored_clause18440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24649
  ] at hbad
  tauto

theorem fin15Anchored_clause18441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom2435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24649
  ] at hbad
  tauto

theorem fin15Anchored_clause18442 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom0626 Fin15AnchoredAtom0654
    Fin15AnchoredAtom0763 Fin15AnchoredAtom1434 Fin15AnchoredAtom2435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24649
  ] at hbad
  tauto

theorem fin15Anchored_clause18443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom2436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00905
  ] at hbad
  tauto

theorem fin15Anchored_clause18444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00905
  ] at hbad
  tauto

theorem fin15Anchored_clause18445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom2436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00905
  ] at hbad
  tauto

theorem fin15Anchored_clause18446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom2436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00905
  ] at hbad
  tauto

theorem fin15Anchored_clause18447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2436 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom2436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00905
  ] at hbad
  tauto

theorem fin15Anchored_clause18448 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom0628 Fin15AnchoredAtom0634
    Fin15AnchoredAtom0764 Fin15AnchoredAtom1435 Fin15AnchoredAtom2436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00905
  ] at hbad
  tauto

theorem fin15Anchored_clause18449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom2437 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01417
  ] at hbad
  tauto

theorem fin15Anchored_clause18450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2437 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01417
  ] at hbad
  tauto

theorem fin15Anchored_clause18451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom2437 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01417
  ] at hbad
  tauto

theorem fin15Anchored_clause18452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom2437 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01417
  ] at hbad
  tauto

theorem fin15Anchored_clause18453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2437 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom2437 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01417
  ] at hbad
  tauto

theorem fin15Anchored_clause18454 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom0629 Fin15AnchoredAtom0635
    Fin15AnchoredAtom0765 Fin15AnchoredAtom1436 Fin15AnchoredAtom2437 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01417
  ] at hbad
  tauto

theorem fin15Anchored_clause18455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom2439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04489
  ] at hbad
  tauto

theorem fin15Anchored_clause18456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04489
  ] at hbad
  tauto

theorem fin15Anchored_clause18457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom2439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04489
  ] at hbad
  tauto

theorem fin15Anchored_clause18458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom2439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04489
  ] at hbad
  tauto

theorem fin15Anchored_clause18459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2439 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom2439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04489
  ] at hbad
  tauto

theorem fin15Anchored_clause18460 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom0631 Fin15AnchoredAtom0637
    Fin15AnchoredAtom0767 Fin15AnchoredAtom1438 Fin15AnchoredAtom2439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04489
  ] at hbad
  tauto

theorem fin15Anchored_clause18461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom2440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08585
  ] at hbad
  tauto

theorem fin15Anchored_clause18462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08585
  ] at hbad
  tauto

theorem fin15Anchored_clause18463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom2440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08585
  ] at hbad
  tauto

theorem fin15Anchored_clause18464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0768 Fin15AnchoredAtom2440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08585
  ] at hbad
  tauto

theorem fin15Anchored_clause18465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2440 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1439 Fin15AnchoredAtom2440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08585
  ] at hbad
  tauto

theorem fin15Anchored_clause18466 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom0632 Fin15AnchoredAtom0638
    Fin15AnchoredAtom0768 Fin15AnchoredAtom1439 Fin15AnchoredAtom2440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08585
  ] at hbad
  tauto

theorem fin15Anchored_clause18467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom2441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16777
  ] at hbad
  tauto

theorem fin15Anchored_clause18468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16777
  ] at hbad
  tauto

theorem fin15Anchored_clause18469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0639 Fin15AnchoredAtom2441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16777
  ] at hbad
  tauto

theorem fin15Anchored_clause18470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0769 Fin15AnchoredAtom2441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16777
  ] at hbad
  tauto

theorem fin15Anchored_clause18471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2441 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1440 Fin15AnchoredAtom2441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16777
  ] at hbad
  tauto

theorem fin15Anchored_clause18472 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom0633 Fin15AnchoredAtom0639
    Fin15AnchoredAtom0769 Fin15AnchoredAtom1440 Fin15AnchoredAtom2441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16777
  ] at hbad
  tauto

theorem fin15Anchored_clause18473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2442 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01673
  ] at hbad
  tauto

theorem fin15Anchored_clause18474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2442 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01673
  ] at hbad
  tauto

theorem fin15Anchored_clause18475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2442 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01673
  ] at hbad
  tauto

theorem fin15Anchored_clause18476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2442 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01673
  ] at hbad
  tauto

theorem fin15Anchored_clause18477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom2442 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01673
  ] at hbad
  tauto

theorem fin15Anchored_clause18478 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom0629 Fin15AnchoredAtom0640
    Fin15AnchoredAtom0770 Fin15AnchoredAtom1441 Fin15AnchoredAtom2442 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01673
  ] at hbad
  tauto

theorem fin15Anchored_clause18479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2443 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02697
  ] at hbad
  tauto

theorem fin15Anchored_clause18480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom0630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0630 Fin15AnchoredAtom2443 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02697
  ] at hbad
  tauto

theorem fin15Anchored_clause18481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom0641 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0641 Fin15AnchoredAtom2443 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02697
  ] at hbad
  tauto

theorem fin15Anchored_clause18482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom2443 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02697
  ] at hbad
  tauto

theorem fin15Anchored_clause18483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2443 chi ∧
      ¬Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1442 Fin15AnchoredAtom2443 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02697
  ] at hbad
  tauto

theorem fin15Anchored_clause18484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2443 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom0630 Fin15AnchoredAtom0641
    Fin15AnchoredAtom0771 Fin15AnchoredAtom1442 Fin15AnchoredAtom2443 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02697
  ] at hbad
  tauto

theorem fin15Anchored_clause18485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04745
  ] at hbad
  tauto

theorem fin15Anchored_clause18486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04745
  ] at hbad
  tauto

theorem fin15Anchored_clause18487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04745
  ] at hbad
  tauto

theorem fin15Anchored_clause18488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04745
  ] at hbad
  tauto

theorem fin15Anchored_clause18489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom2444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04745
  ] at hbad
  tauto

theorem fin15Anchored_clause18490 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom0631 Fin15AnchoredAtom0642
    Fin15AnchoredAtom0772 Fin15AnchoredAtom1443 Fin15AnchoredAtom2444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04745
  ] at hbad
  tauto

theorem fin15Anchored_clause18491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08841
  ] at hbad
  tauto

theorem fin15Anchored_clause18492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08841
  ] at hbad
  tauto

theorem fin15Anchored_clause18493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom2445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08841
  ] at hbad
  tauto

theorem fin15Anchored_clause18494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08841
  ] at hbad
  tauto

theorem fin15Anchored_clause18495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom2445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08841
  ] at hbad
  tauto

theorem fin15Anchored_clause18496 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom0632 Fin15AnchoredAtom0643
    Fin15AnchoredAtom0773 Fin15AnchoredAtom1444 Fin15AnchoredAtom2445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08841
  ] at hbad
  tauto

theorem fin15Anchored_clause18497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17033
  ] at hbad
  tauto

theorem fin15Anchored_clause18498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17033
  ] at hbad
  tauto

theorem fin15Anchored_clause18499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom2446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17033
  ] at hbad
  tauto

theorem fin15Anchored_clause18500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17033
  ] at hbad
  tauto

theorem fin15Anchored_clause18501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom2446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17033
  ] at hbad
  tauto

theorem fin15Anchored_clause18502 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom0633 Fin15AnchoredAtom0644
    Fin15AnchoredAtom0774 Fin15AnchoredAtom1445 Fin15AnchoredAtom2446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17033
  ] at hbad
  tauto

theorem fin15Anchored_clause18503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03209
  ] at hbad
  tauto

theorem fin15Anchored_clause18504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom0630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0630 Fin15AnchoredAtom2447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03209
  ] at hbad
  tauto

theorem fin15Anchored_clause18505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom0645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0645 Fin15AnchoredAtom2447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03209
  ] at hbad
  tauto

theorem fin15Anchored_clause18506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03209
  ] at hbad
  tauto

theorem fin15Anchored_clause18507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2447 chi ∧
      ¬Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1446 Fin15AnchoredAtom2447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03209
  ] at hbad
  tauto

theorem fin15Anchored_clause18508 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2447 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom0630 Fin15AnchoredAtom0645
    Fin15AnchoredAtom0775 Fin15AnchoredAtom1446 Fin15AnchoredAtom2447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03209
  ] at hbad
  tauto

theorem fin15Anchored_clause18509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05257
  ] at hbad
  tauto

theorem fin15Anchored_clause18510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05257
  ] at hbad
  tauto

theorem fin15Anchored_clause18511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05257
  ] at hbad
  tauto

theorem fin15Anchored_clause18512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05257
  ] at hbad
  tauto

theorem fin15Anchored_clause18513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom2448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05257
  ] at hbad
  tauto

theorem fin15Anchored_clause18514 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom0631 Fin15AnchoredAtom0646
    Fin15AnchoredAtom0776 Fin15AnchoredAtom1447 Fin15AnchoredAtom2448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05257
  ] at hbad
  tauto

theorem fin15Anchored_clause18515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09353
  ] at hbad
  tauto

theorem fin15Anchored_clause18516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09353
  ] at hbad
  tauto

theorem fin15Anchored_clause18517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09353
  ] at hbad
  tauto

theorem fin15Anchored_clause18518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09353
  ] at hbad
  tauto

theorem fin15Anchored_clause18519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom2449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09353
  ] at hbad
  tauto

theorem fin15Anchored_clause18520 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom0632 Fin15AnchoredAtom0647
    Fin15AnchoredAtom0777 Fin15AnchoredAtom1448 Fin15AnchoredAtom2449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09353
  ] at hbad
  tauto

theorem fin15Anchored_clause18521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17545
  ] at hbad
  tauto

theorem fin15Anchored_clause18522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17545
  ] at hbad
  tauto

theorem fin15Anchored_clause18523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17545
  ] at hbad
  tauto

theorem fin15Anchored_clause18524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17545
  ] at hbad
  tauto

theorem fin15Anchored_clause18525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom2450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17545
  ] at hbad
  tauto

theorem fin15Anchored_clause18526 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom0633 Fin15AnchoredAtom0648
    Fin15AnchoredAtom0778 Fin15AnchoredAtom1449 Fin15AnchoredAtom2450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17545
  ] at hbad
  tauto

theorem fin15Anchored_clause18527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06281
  ] at hbad
  tauto

theorem fin15Anchored_clause18528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom0649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0649 Fin15AnchoredAtom2451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06281
  ] at hbad
  tauto

theorem fin15Anchored_clause18529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2451 chi ∧
      ¬Fin15AnchoredAtom0779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0779 Fin15AnchoredAtom2451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06281
  ] at hbad
  tauto

theorem fin15Anchored_clause18530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2452 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10377
  ] at hbad
  tauto

theorem fin15Anchored_clause18531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2452 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0780 Fin15AnchoredAtom2452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10377
  ] at hbad
  tauto

theorem fin15Anchored_clause18532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom0630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0630 Fin15AnchoredAtom2453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18569
  ] at hbad
  tauto

theorem fin15Anchored_clause18533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18569
  ] at hbad
  tauto

theorem fin15Anchored_clause18534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom0651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0651 Fin15AnchoredAtom2453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18569
  ] at hbad
  tauto

theorem fin15Anchored_clause18535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom0781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0781 Fin15AnchoredAtom2453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18569
  ] at hbad
  tauto

theorem fin15Anchored_clause18536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2453 chi ∧
      ¬Fin15AnchoredAtom1452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1452 Fin15AnchoredAtom2453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18569
  ] at hbad
  tauto

theorem fin15Anchored_clause18537 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2453 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom1452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0630 Fin15AnchoredAtom0633 Fin15AnchoredAtom0651
    Fin15AnchoredAtom0781 Fin15AnchoredAtom1452 Fin15AnchoredAtom2453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18569
  ] at hbad
  tauto

theorem fin15Anchored_clause18538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12425
  ] at hbad
  tauto

theorem fin15Anchored_clause18539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12425
  ] at hbad
  tauto

theorem fin15Anchored_clause18540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12425
  ] at hbad
  tauto

theorem fin15Anchored_clause18541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12425
  ] at hbad
  tauto

theorem fin15Anchored_clause18542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom2454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12425
  ] at hbad
  tauto

theorem fin15Anchored_clause18543 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom0632 Fin15AnchoredAtom0652
    Fin15AnchoredAtom0782 Fin15AnchoredAtom1453 Fin15AnchoredAtom2454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12425
  ] at hbad
  tauto

theorem fin15Anchored_clause18544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20617
  ] at hbad
  tauto

theorem fin15Anchored_clause18545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20617
  ] at hbad
  tauto

theorem fin15Anchored_clause18546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20617
  ] at hbad
  tauto

theorem fin15Anchored_clause18547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20617
  ] at hbad
  tauto

theorem fin15Anchored_clause18548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom2455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20617
  ] at hbad
  tauto

theorem fin15Anchored_clause18549 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom0633 Fin15AnchoredAtom0653
    Fin15AnchoredAtom0783 Fin15AnchoredAtom1454 Fin15AnchoredAtom2455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20617
  ] at hbad
  tauto

theorem fin15Anchored_clause18550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24713
  ] at hbad
  tauto

theorem fin15Anchored_clause18551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24713
  ] at hbad
  tauto

theorem fin15Anchored_clause18552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24713
  ] at hbad
  tauto

theorem fin15Anchored_clause18553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24713
  ] at hbad
  tauto

theorem fin15Anchored_clause18554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom2456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24713
  ] at hbad
  tauto

theorem fin15Anchored_clause18555 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom0633 Fin15AnchoredAtom0654
    Fin15AnchoredAtom0784 Fin15AnchoredAtom1455 Fin15AnchoredAtom2456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24713
  ] at hbad
  tauto

theorem fin15Anchored_clause18556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom2457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01801
  ] at hbad
  tauto

theorem fin15Anchored_clause18557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom2457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01801
  ] at hbad
  tauto

theorem fin15Anchored_clause18558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01801
  ] at hbad
  tauto

theorem fin15Anchored_clause18559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom2457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01801
  ] at hbad
  tauto

end ErdosSzekeres

end
