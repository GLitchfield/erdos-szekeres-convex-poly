module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 121. -/

theorem fin15Anchored_clause15488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04119
  ] at hbad
  tauto

theorem fin15Anchored_clause15489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04119
  ] at hbad
  tauto

theorem fin15Anchored_clause15490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04119
  ] at hbad
  tauto

theorem fin15Anchored_clause15491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0552 Fin15AnchoredAtom1839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04119
  ] at hbad
  tauto

theorem fin15Anchored_clause15492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom1839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04119
  ] at hbad
  tauto

theorem fin15Anchored_clause15493 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1839 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0552 chi ∧
      Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0465 Fin15AnchoredAtom0486
    Fin15AnchoredAtom0552 Fin15AnchoredAtom0838 Fin15AnchoredAtom1839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04119
  ] at hbad
  tauto

theorem fin15Anchored_clause15494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08215
  ] at hbad
  tauto

theorem fin15Anchored_clause15495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom1840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08215
  ] at hbad
  tauto

theorem fin15Anchored_clause15496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08215
  ] at hbad
  tauto

theorem fin15Anchored_clause15497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0553 Fin15AnchoredAtom1840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08215
  ] at hbad
  tauto

theorem fin15Anchored_clause15498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom1840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08215
  ] at hbad
  tauto

theorem fin15Anchored_clause15499 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1840 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0553 chi ∧
      Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0466 Fin15AnchoredAtom0487
    Fin15AnchoredAtom0553 Fin15AnchoredAtom0839 Fin15AnchoredAtom1840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08215
  ] at hbad
  tauto

theorem fin15Anchored_clause15500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0457 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom1841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16407
  ] at hbad
  tauto

theorem fin15Anchored_clause15501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0467 Fin15AnchoredAtom1841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16407
  ] at hbad
  tauto

theorem fin15Anchored_clause15502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16407
  ] at hbad
  tauto

theorem fin15Anchored_clause15503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom1841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16407
  ] at hbad
  tauto

theorem fin15Anchored_clause15504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom1841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16407
  ] at hbad
  tauto

theorem fin15Anchored_clause15505 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1841 chi ∧
      Fin15AnchoredAtom0457 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0457 Fin15AnchoredAtom0467 Fin15AnchoredAtom0488
    Fin15AnchoredAtom0554 Fin15AnchoredAtom0840 Fin15AnchoredAtom1841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16407
  ] at hbad
  tauto

theorem fin15Anchored_clause15506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00103
  ] at hbad
  tauto

theorem fin15Anchored_clause15507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00103
  ] at hbad
  tauto

theorem fin15Anchored_clause15508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00103
  ] at hbad
  tauto

theorem fin15Anchored_clause15509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom1842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00103
  ] at hbad
  tauto

theorem fin15Anchored_clause15510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom1842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00103
  ] at hbad
  tauto

theorem fin15Anchored_clause15511 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1842 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom0459 Fin15AnchoredAtom0489
    Fin15AnchoredAtom0555 Fin15AnchoredAtom0841 Fin15AnchoredAtom1842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00103
  ] at hbad
  tauto

theorem fin15Anchored_clause15512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00167
  ] at hbad
  tauto

theorem fin15Anchored_clause15513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00167
  ] at hbad
  tauto

theorem fin15Anchored_clause15514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom1843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00167
  ] at hbad
  tauto

theorem fin15Anchored_clause15515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom1843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00167
  ] at hbad
  tauto

theorem fin15Anchored_clause15516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom1843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00167
  ] at hbad
  tauto

theorem fin15Anchored_clause15517 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1843 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom0460 Fin15AnchoredAtom0490
    Fin15AnchoredAtom0556 Fin15AnchoredAtom0842 Fin15AnchoredAtom1843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00167
  ] at hbad
  tauto

theorem fin15Anchored_clause15518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1844 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00295
  ] at hbad
  tauto

theorem fin15Anchored_clause15519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1844 chi ∧
      ¬Fin15AnchoredAtom0461 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0461 Fin15AnchoredAtom1844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00295
  ] at hbad
  tauto

theorem fin15Anchored_clause15520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1844 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom1844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00295
  ] at hbad
  tauto

theorem fin15Anchored_clause15521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1844 chi ∧
      ¬Fin15AnchoredAtom0843 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0843 Fin15AnchoredAtom1844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00295
  ] at hbad
  tauto

theorem fin15Anchored_clause15522 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1844 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0843 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom0461 Fin15AnchoredAtom0491
    Fin15AnchoredAtom0557 Fin15AnchoredAtom0843 Fin15AnchoredAtom1844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00295
  ] at hbad
  tauto

theorem fin15Anchored_clause15523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1845 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00551
  ] at hbad
  tauto

theorem fin15Anchored_clause15524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1845 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00551
  ] at hbad
  tauto

theorem fin15Anchored_clause15525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom1845 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00551
  ] at hbad
  tauto

theorem fin15Anchored_clause15526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom1845 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00551
  ] at hbad
  tauto

theorem fin15Anchored_clause15527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom1845 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00551
  ] at hbad
  tauto

theorem fin15Anchored_clause15528 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1845 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom0462 Fin15AnchoredAtom0492
    Fin15AnchoredAtom0558 Fin15AnchoredAtom0844 Fin15AnchoredAtom1845 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00551
  ] at hbad
  tauto

theorem fin15Anchored_clause15529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01063
  ] at hbad
  tauto

theorem fin15Anchored_clause15530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01063
  ] at hbad
  tauto

theorem fin15Anchored_clause15531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom1846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01063
  ] at hbad
  tauto

theorem fin15Anchored_clause15532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom1846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01063
  ] at hbad
  tauto

theorem fin15Anchored_clause15533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom1846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01063
  ] at hbad
  tauto

theorem fin15Anchored_clause15534 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1846 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom0463 Fin15AnchoredAtom0493
    Fin15AnchoredAtom0559 Fin15AnchoredAtom0845 Fin15AnchoredAtom1846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01063
  ] at hbad
  tauto

theorem fin15Anchored_clause15535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02087
  ] at hbad
  tauto

theorem fin15Anchored_clause15536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom0494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0494 Fin15AnchoredAtom1847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02087
  ] at hbad
  tauto

theorem fin15Anchored_clause15537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom0560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0560 Fin15AnchoredAtom1847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02087
  ] at hbad
  tauto

theorem fin15Anchored_clause15538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1847 chi ∧
      ¬Fin15AnchoredAtom0846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0846 Fin15AnchoredAtom1847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02087
  ] at hbad
  tauto

theorem fin15Anchored_clause15539 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1847 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom0464 Fin15AnchoredAtom0494
    Fin15AnchoredAtom0560 Fin15AnchoredAtom0846 Fin15AnchoredAtom1847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02087
  ] at hbad
  tauto

theorem fin15Anchored_clause15540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04135
  ] at hbad
  tauto

theorem fin15Anchored_clause15541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04135
  ] at hbad
  tauto

theorem fin15Anchored_clause15542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom1848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04135
  ] at hbad
  tauto

theorem fin15Anchored_clause15543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom1848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04135
  ] at hbad
  tauto

theorem fin15Anchored_clause15544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom1848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04135
  ] at hbad
  tauto

theorem fin15Anchored_clause15545 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1848 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom0465 Fin15AnchoredAtom0495
    Fin15AnchoredAtom0561 Fin15AnchoredAtom0847 Fin15AnchoredAtom1848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04135
  ] at hbad
  tauto

theorem fin15Anchored_clause15546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08231
  ] at hbad
  tauto

theorem fin15Anchored_clause15547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom1849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08231
  ] at hbad
  tauto

theorem fin15Anchored_clause15548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom1849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08231
  ] at hbad
  tauto

theorem fin15Anchored_clause15549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom1849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08231
  ] at hbad
  tauto

theorem fin15Anchored_clause15550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom1849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08231
  ] at hbad
  tauto

theorem fin15Anchored_clause15551 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1849 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom0466 Fin15AnchoredAtom0496
    Fin15AnchoredAtom0562 Fin15AnchoredAtom0848 Fin15AnchoredAtom1849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08231
  ] at hbad
  tauto

theorem fin15Anchored_clause15552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom1850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16423
  ] at hbad
  tauto

theorem fin15Anchored_clause15553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0467 Fin15AnchoredAtom1850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16423
  ] at hbad
  tauto

theorem fin15Anchored_clause15554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom1850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16423
  ] at hbad
  tauto

theorem fin15Anchored_clause15555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom1850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16423
  ] at hbad
  tauto

theorem fin15Anchored_clause15556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0849 Fin15AnchoredAtom1850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16423
  ] at hbad
  tauto

theorem fin15Anchored_clause15557 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1850 chi ∧
      Fin15AnchoredAtom0458 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0458 Fin15AnchoredAtom0467 Fin15AnchoredAtom0497
    Fin15AnchoredAtom0563 Fin15AnchoredAtom0849 Fin15AnchoredAtom1850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16423
  ] at hbad
  tauto

theorem fin15Anchored_clause15558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00199
  ] at hbad
  tauto

theorem fin15Anchored_clause15559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00199
  ] at hbad
  tauto

theorem fin15Anchored_clause15560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom1851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00199
  ] at hbad
  tauto

theorem fin15Anchored_clause15561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom1851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00199
  ] at hbad
  tauto

theorem fin15Anchored_clause15562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom1851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00199
  ] at hbad
  tauto

theorem fin15Anchored_clause15563 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1851 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom0460 Fin15AnchoredAtom0498
    Fin15AnchoredAtom0564 Fin15AnchoredAtom0850 Fin15AnchoredAtom1851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00199
  ] at hbad
  tauto

theorem fin15Anchored_clause15564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1852 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00327
  ] at hbad
  tauto

theorem fin15Anchored_clause15565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0461 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0461 Fin15AnchoredAtom1852 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00327
  ] at hbad
  tauto

theorem fin15Anchored_clause15566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom1852 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00327
  ] at hbad
  tauto

theorem fin15Anchored_clause15567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0565 Fin15AnchoredAtom1852 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00327
  ] at hbad
  tauto

theorem fin15Anchored_clause15568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1852 chi ∧
      ¬Fin15AnchoredAtom0851 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0851 Fin15AnchoredAtom1852 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00327
  ] at hbad
  tauto

theorem fin15Anchored_clause15569 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1852 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0851 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom0461 Fin15AnchoredAtom0499
    Fin15AnchoredAtom0565 Fin15AnchoredAtom0851 Fin15AnchoredAtom1852 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00327
  ] at hbad
  tauto

theorem fin15Anchored_clause15570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00583
  ] at hbad
  tauto

theorem fin15Anchored_clause15571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00583
  ] at hbad
  tauto

theorem fin15Anchored_clause15572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom1853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00583
  ] at hbad
  tauto

theorem fin15Anchored_clause15573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom1853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00583
  ] at hbad
  tauto

theorem fin15Anchored_clause15574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom1853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00583
  ] at hbad
  tauto

theorem fin15Anchored_clause15575 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1853 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom0462 Fin15AnchoredAtom0500
    Fin15AnchoredAtom0566 Fin15AnchoredAtom0852 Fin15AnchoredAtom1853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00583
  ] at hbad
  tauto

theorem fin15Anchored_clause15576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01095
  ] at hbad
  tauto

theorem fin15Anchored_clause15577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01095
  ] at hbad
  tauto

theorem fin15Anchored_clause15578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom1854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01095
  ] at hbad
  tauto

theorem fin15Anchored_clause15579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom1854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01095
  ] at hbad
  tauto

theorem fin15Anchored_clause15580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom1854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01095
  ] at hbad
  tauto

theorem fin15Anchored_clause15581 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1854 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom0463 Fin15AnchoredAtom0501
    Fin15AnchoredAtom0567 Fin15AnchoredAtom0853 Fin15AnchoredAtom1854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01095
  ] at hbad
  tauto

theorem fin15Anchored_clause15582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1855 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1855 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02119
  ] at hbad
  tauto

theorem fin15Anchored_clause15583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1855 chi ∧
      ¬Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0854 Fin15AnchoredAtom1855 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02119
  ] at hbad
  tauto

theorem fin15Anchored_clause15584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1855 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0502 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom0464 Fin15AnchoredAtom0502
    Fin15AnchoredAtom0568 Fin15AnchoredAtom0854 Fin15AnchoredAtom1855 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02119
  ] at hbad
  tauto

theorem fin15Anchored_clause15585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04167
  ] at hbad
  tauto

theorem fin15Anchored_clause15586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04167
  ] at hbad
  tauto

theorem fin15Anchored_clause15587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom1856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04167
  ] at hbad
  tauto

theorem fin15Anchored_clause15588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom1856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04167
  ] at hbad
  tauto

theorem fin15Anchored_clause15589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom1856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04167
  ] at hbad
  tauto

theorem fin15Anchored_clause15590 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1856 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom0465 Fin15AnchoredAtom0503
    Fin15AnchoredAtom0569 Fin15AnchoredAtom0855 Fin15AnchoredAtom1856 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04167
  ] at hbad
  tauto

theorem fin15Anchored_clause15591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1857 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08263
  ] at hbad
  tauto

theorem fin15Anchored_clause15592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom1857 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08263
  ] at hbad
  tauto

theorem fin15Anchored_clause15593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom1857 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08263
  ] at hbad
  tauto

theorem fin15Anchored_clause15594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom1857 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08263
  ] at hbad
  tauto

theorem fin15Anchored_clause15595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom1857 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08263
  ] at hbad
  tauto

theorem fin15Anchored_clause15596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1857 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom0466 Fin15AnchoredAtom0504
    Fin15AnchoredAtom0570 Fin15AnchoredAtom0856 Fin15AnchoredAtom1857 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08263
  ] at hbad
  tauto

theorem fin15Anchored_clause15597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom1858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16455
  ] at hbad
  tauto

theorem fin15Anchored_clause15598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0467 Fin15AnchoredAtom1858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16455
  ] at hbad
  tauto

theorem fin15Anchored_clause15599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom1858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16455
  ] at hbad
  tauto

theorem fin15Anchored_clause15600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom1858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16455
  ] at hbad
  tauto

theorem fin15Anchored_clause15601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom1858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16455
  ] at hbad
  tauto

theorem fin15Anchored_clause15602 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1858 chi ∧
      Fin15AnchoredAtom0459 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0459 Fin15AnchoredAtom0467 Fin15AnchoredAtom0505
    Fin15AnchoredAtom0571 Fin15AnchoredAtom0857 Fin15AnchoredAtom1858 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16455
  ] at hbad
  tauto

theorem fin15Anchored_clause15603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1859 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00391
  ] at hbad
  tauto

theorem fin15Anchored_clause15604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1859 chi ∧
      ¬Fin15AnchoredAtom0461 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0461 Fin15AnchoredAtom1859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00391
  ] at hbad
  tauto

theorem fin15Anchored_clause15605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1859 chi ∧
      ¬Fin15AnchoredAtom0572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0572 Fin15AnchoredAtom1859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00391
  ] at hbad
  tauto

theorem fin15Anchored_clause15606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1859 chi ∧
      ¬Fin15AnchoredAtom0858 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0858 Fin15AnchoredAtom1859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00391
  ] at hbad
  tauto

theorem fin15Anchored_clause15607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1859 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0858 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom0461 Fin15AnchoredAtom0506
    Fin15AnchoredAtom0572 Fin15AnchoredAtom0858 Fin15AnchoredAtom1859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00391
  ] at hbad
  tauto

theorem fin15Anchored_clause15608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00647
  ] at hbad
  tauto

theorem fin15Anchored_clause15609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00647
  ] at hbad
  tauto

theorem fin15Anchored_clause15610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom1860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00647
  ] at hbad
  tauto

theorem fin15Anchored_clause15611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom1860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00647
  ] at hbad
  tauto

theorem fin15Anchored_clause15612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom1860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00647
  ] at hbad
  tauto

theorem fin15Anchored_clause15613 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1860 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom0462 Fin15AnchoredAtom0507
    Fin15AnchoredAtom0573 Fin15AnchoredAtom0859 Fin15AnchoredAtom1860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00647
  ] at hbad
  tauto

theorem fin15Anchored_clause15614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01159
  ] at hbad
  tauto

theorem fin15Anchored_clause15615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01159
  ] at hbad
  tauto

end ErdosSzekeres

end
