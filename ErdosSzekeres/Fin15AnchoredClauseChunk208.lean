module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 208. -/

theorem fin15Anchored_clause26624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom4413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04912
  ] at hbad
  tauto

theorem fin15Anchored_clause26625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom4413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04912
  ] at hbad
  tauto

theorem fin15Anchored_clause26626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom4413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04912
  ] at hbad
  tauto

theorem fin15Anchored_clause26627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom4413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04912
  ] at hbad
  tauto

theorem fin15Anchored_clause26628 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4413 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom1509 Fin15AnchoredAtom1514
    Fin15AnchoredAtom1578 Fin15AnchoredAtom1662 Fin15AnchoredAtom4413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04912
  ] at hbad
  tauto

theorem fin15Anchored_clause26629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom4414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09008
  ] at hbad
  tauto

theorem fin15Anchored_clause26630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom4414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09008
  ] at hbad
  tauto

theorem fin15Anchored_clause26631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom4414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09008
  ] at hbad
  tauto

theorem fin15Anchored_clause26632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1579 Fin15AnchoredAtom4414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09008
  ] at hbad
  tauto

theorem fin15Anchored_clause26633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4414 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom4414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09008
  ] at hbad
  tauto

theorem fin15Anchored_clause26634 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom1510 Fin15AnchoredAtom1515
    Fin15AnchoredAtom1579 Fin15AnchoredAtom1663 Fin15AnchoredAtom4414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09008
  ] at hbad
  tauto

theorem fin15Anchored_clause26635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom4415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17200
  ] at hbad
  tauto

theorem fin15Anchored_clause26636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1511 Fin15AnchoredAtom4415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17200
  ] at hbad
  tauto

theorem fin15Anchored_clause26637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom4415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17200
  ] at hbad
  tauto

theorem fin15Anchored_clause26638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4415 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1664 Fin15AnchoredAtom4415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17200
  ] at hbad
  tauto

theorem fin15Anchored_clause26639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4415 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom1511 Fin15AnchoredAtom1516
    Fin15AnchoredAtom1580 Fin15AnchoredAtom1664 Fin15AnchoredAtom4415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17200
  ] at hbad
  tauto

theorem fin15Anchored_clause26640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom4417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05424
  ] at hbad
  tauto

theorem fin15Anchored_clause26641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom4417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05424
  ] at hbad
  tauto

theorem fin15Anchored_clause26642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom4417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05424
  ] at hbad
  tauto

theorem fin15Anchored_clause26643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom4417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05424
  ] at hbad
  tauto

theorem fin15Anchored_clause26644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4417 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom4417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05424
  ] at hbad
  tauto

theorem fin15Anchored_clause26645 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom1509 Fin15AnchoredAtom1518
    Fin15AnchoredAtom1582 Fin15AnchoredAtom1666 Fin15AnchoredAtom4417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05424
  ] at hbad
  tauto

theorem fin15Anchored_clause26646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom4418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09520
  ] at hbad
  tauto

theorem fin15Anchored_clause26647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom4418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09520
  ] at hbad
  tauto

theorem fin15Anchored_clause26648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom4418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09520
  ] at hbad
  tauto

theorem fin15Anchored_clause26649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom4418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09520
  ] at hbad
  tauto

theorem fin15Anchored_clause26650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4418 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom4418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09520
  ] at hbad
  tauto

theorem fin15Anchored_clause26651 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom1510 Fin15AnchoredAtom1519
    Fin15AnchoredAtom1583 Fin15AnchoredAtom1667 Fin15AnchoredAtom4418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09520
  ] at hbad
  tauto

theorem fin15Anchored_clause26652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom4419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17712
  ] at hbad
  tauto

theorem fin15Anchored_clause26653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1511 Fin15AnchoredAtom4419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17712
  ] at hbad
  tauto

theorem fin15Anchored_clause26654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom4419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17712
  ] at hbad
  tauto

theorem fin15Anchored_clause26655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1584 Fin15AnchoredAtom4419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17712
  ] at hbad
  tauto

theorem fin15Anchored_clause26656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4419 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1668 Fin15AnchoredAtom4419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17712
  ] at hbad
  tauto

theorem fin15Anchored_clause26657 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4419 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom1511 Fin15AnchoredAtom1520
    Fin15AnchoredAtom1584 Fin15AnchoredAtom1668 Fin15AnchoredAtom4419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17712
  ] at hbad
  tauto

theorem fin15Anchored_clause26658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom4423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12592
  ] at hbad
  tauto

theorem fin15Anchored_clause26659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom4423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12592
  ] at hbad
  tauto

theorem fin15Anchored_clause26660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom4423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12592
  ] at hbad
  tauto

theorem fin15Anchored_clause26661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom4423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12592
  ] at hbad
  tauto

theorem fin15Anchored_clause26662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4423 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom4423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12592
  ] at hbad
  tauto

theorem fin15Anchored_clause26663 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom1510 Fin15AnchoredAtom1524
    Fin15AnchoredAtom1588 Fin15AnchoredAtom1672 Fin15AnchoredAtom4423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12592
  ] at hbad
  tauto

theorem fin15Anchored_clause26664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom4424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20784
  ] at hbad
  tauto

theorem fin15Anchored_clause26665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1511 Fin15AnchoredAtom4424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20784
  ] at hbad
  tauto

theorem fin15Anchored_clause26666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom4424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20784
  ] at hbad
  tauto

theorem fin15Anchored_clause26667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4424 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1673 Fin15AnchoredAtom4424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20784
  ] at hbad
  tauto

theorem fin15Anchored_clause26668 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4424 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom1511 Fin15AnchoredAtom1525
    Fin15AnchoredAtom1589 Fin15AnchoredAtom1673 Fin15AnchoredAtom4424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20784
  ] at hbad
  tauto

theorem fin15Anchored_clause26669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom4425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24880
  ] at hbad
  tauto

theorem fin15Anchored_clause26670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1511 Fin15AnchoredAtom4425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24880
  ] at hbad
  tauto

theorem fin15Anchored_clause26671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom4425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24880
  ] at hbad
  tauto

theorem fin15Anchored_clause26672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom4425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24880
  ] at hbad
  tauto

theorem fin15Anchored_clause26673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4425 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1674 Fin15AnchoredAtom4425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24880
  ] at hbad
  tauto

theorem fin15Anchored_clause26674 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom1511 Fin15AnchoredAtom1526
    Fin15AnchoredAtom1590 Fin15AnchoredAtom1674 Fin15AnchoredAtom4425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24880
  ] at hbad
  tauto

theorem fin15Anchored_clause26675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1591 Fin15AnchoredAtom4426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03632
  ] at hbad
  tauto

theorem fin15Anchored_clause26676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4426 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom4426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03632
  ] at hbad
  tauto

theorem fin15Anchored_clause26677 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4426 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1591 chi ∧
      Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom1513 Fin15AnchoredAtom1517
    Fin15AnchoredAtom1591 Fin15AnchoredAtom1675 Fin15AnchoredAtom4426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03632
  ] at hbad
  tauto

theorem fin15Anchored_clause26678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom4427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05680
  ] at hbad
  tauto

theorem fin15Anchored_clause26679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom4427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05680
  ] at hbad
  tauto

theorem fin15Anchored_clause26680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom4427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05680
  ] at hbad
  tauto

theorem fin15Anchored_clause26681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom4427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05680
  ] at hbad
  tauto

theorem fin15Anchored_clause26682 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4427 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom4427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05680
  ] at hbad
  tauto

theorem fin15Anchored_clause26683 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom1514 Fin15AnchoredAtom1518
    Fin15AnchoredAtom1592 Fin15AnchoredAtom1676 Fin15AnchoredAtom4427 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05680
  ] at hbad
  tauto

theorem fin15Anchored_clause26684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom4428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09776
  ] at hbad
  tauto

theorem fin15Anchored_clause26685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom4428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09776
  ] at hbad
  tauto

theorem fin15Anchored_clause26686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom4428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09776
  ] at hbad
  tauto

theorem fin15Anchored_clause26687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom4428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09776
  ] at hbad
  tauto

theorem fin15Anchored_clause26688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4428 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom4428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09776
  ] at hbad
  tauto

theorem fin15Anchored_clause26689 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom1515 Fin15AnchoredAtom1519
    Fin15AnchoredAtom1593 Fin15AnchoredAtom1677 Fin15AnchoredAtom4428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09776
  ] at hbad
  tauto

theorem fin15Anchored_clause26690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom4429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17968
  ] at hbad
  tauto

theorem fin15Anchored_clause26691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom4429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17968
  ] at hbad
  tauto

theorem fin15Anchored_clause26692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom4429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17968
  ] at hbad
  tauto

theorem fin15Anchored_clause26693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom4429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17968
  ] at hbad
  tauto

theorem fin15Anchored_clause26694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4429 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom4429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17968
  ] at hbad
  tauto

theorem fin15Anchored_clause26695 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom1516 Fin15AnchoredAtom1520
    Fin15AnchoredAtom1594 Fin15AnchoredAtom1678 Fin15AnchoredAtom4429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17968
  ] at hbad
  tauto

theorem fin15Anchored_clause26696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1521 Fin15AnchoredAtom4430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06704
  ] at hbad
  tauto

theorem fin15Anchored_clause26697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1595 Fin15AnchoredAtom4430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06704
  ] at hbad
  tauto

theorem fin15Anchored_clause26698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4430 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1679 Fin15AnchoredAtom4430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06704
  ] at hbad
  tauto

theorem fin15Anchored_clause26699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4430 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1595 chi ∧
      Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1513 Fin15AnchoredAtom1514 Fin15AnchoredAtom1521
    Fin15AnchoredAtom1595 Fin15AnchoredAtom1679 Fin15AnchoredAtom4430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06704
  ] at hbad
  tauto

theorem fin15Anchored_clause26700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1513 Fin15AnchoredAtom4431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10800
  ] at hbad
  tauto

theorem fin15Anchored_clause26701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1596 Fin15AnchoredAtom4431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10800
  ] at hbad
  tauto

theorem fin15Anchored_clause26702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4431 chi ∧
      ¬Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1680 Fin15AnchoredAtom4431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10800
  ] at hbad
  tauto

theorem fin15Anchored_clause26703 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4431 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1522 chi ∧
      Fin15AnchoredAtom1596 chi ∧
      Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1513 Fin15AnchoredAtom1515 Fin15AnchoredAtom1522
    Fin15AnchoredAtom1596 Fin15AnchoredAtom1680 Fin15AnchoredAtom4431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10800
  ] at hbad
  tauto

theorem fin15Anchored_clause26704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4432 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom4432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18992
  ] at hbad
  tauto

theorem fin15Anchored_clause26705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4432 chi ∧
      ¬Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1597 Fin15AnchoredAtom4432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18992
  ] at hbad
  tauto

theorem fin15Anchored_clause26706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4432 chi ∧
      ¬Fin15AnchoredAtom1681 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1681 Fin15AnchoredAtom4432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18992
  ] at hbad
  tauto

theorem fin15Anchored_clause26707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4432 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1523 chi ∧
      Fin15AnchoredAtom1597 chi ∧
      Fin15AnchoredAtom1681 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1513 Fin15AnchoredAtom1516 Fin15AnchoredAtom1523
    Fin15AnchoredAtom1597 Fin15AnchoredAtom1681 Fin15AnchoredAtom4432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18992
  ] at hbad
  tauto

theorem fin15Anchored_clause26708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom4433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12848
  ] at hbad
  tauto

theorem fin15Anchored_clause26709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom4433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12848
  ] at hbad
  tauto

theorem fin15Anchored_clause26710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom4433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12848
  ] at hbad
  tauto

theorem fin15Anchored_clause26711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom4433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12848
  ] at hbad
  tauto

theorem fin15Anchored_clause26712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4433 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom4433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12848
  ] at hbad
  tauto

theorem fin15Anchored_clause26713 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom1515 Fin15AnchoredAtom1524
    Fin15AnchoredAtom1598 Fin15AnchoredAtom1682 Fin15AnchoredAtom4433 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12848
  ] at hbad
  tauto

theorem fin15Anchored_clause26714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom4434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21040
  ] at hbad
  tauto

theorem fin15Anchored_clause26715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom4434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21040
  ] at hbad
  tauto

theorem fin15Anchored_clause26716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom4434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21040
  ] at hbad
  tauto

theorem fin15Anchored_clause26717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom4434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21040
  ] at hbad
  tauto

theorem fin15Anchored_clause26718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4434 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom4434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21040
  ] at hbad
  tauto

theorem fin15Anchored_clause26719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom1516 Fin15AnchoredAtom1525
    Fin15AnchoredAtom1599 Fin15AnchoredAtom1683 Fin15AnchoredAtom4434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21040
  ] at hbad
  tauto

theorem fin15Anchored_clause26720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom4435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25136
  ] at hbad
  tauto

theorem fin15Anchored_clause26721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom4435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25136
  ] at hbad
  tauto

theorem fin15Anchored_clause26722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom4435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25136
  ] at hbad
  tauto

theorem fin15Anchored_clause26723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom4435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25136
  ] at hbad
  tauto

theorem fin15Anchored_clause26724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4435 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom4435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25136
  ] at hbad
  tauto

theorem fin15Anchored_clause26725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom1516 Fin15AnchoredAtom1526
    Fin15AnchoredAtom1600 Fin15AnchoredAtom1684 Fin15AnchoredAtom4435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25136
  ] at hbad
  tauto

theorem fin15Anchored_clause26726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom4436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07216
  ] at hbad
  tauto

theorem fin15Anchored_clause26727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1521 Fin15AnchoredAtom4436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07216
  ] at hbad
  tauto

theorem fin15Anchored_clause26728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1601 Fin15AnchoredAtom4436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07216
  ] at hbad
  tauto

theorem fin15Anchored_clause26729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4436 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1685 Fin15AnchoredAtom4436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07216
  ] at hbad
  tauto

theorem fin15Anchored_clause26730 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4436 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1601 chi ∧
      Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1517 Fin15AnchoredAtom1518 Fin15AnchoredAtom1521
    Fin15AnchoredAtom1601 Fin15AnchoredAtom1685 Fin15AnchoredAtom4436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07216
  ] at hbad
  tauto

theorem fin15Anchored_clause26731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4437 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom4437 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11312
  ] at hbad
  tauto

theorem fin15Anchored_clause26732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4437 chi ∧
      ¬Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1686 Fin15AnchoredAtom4437 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11312
  ] at hbad
  tauto

theorem fin15Anchored_clause26733 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4437 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1522 chi ∧
      Fin15AnchoredAtom1602 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1517 Fin15AnchoredAtom1519 Fin15AnchoredAtom1522
    Fin15AnchoredAtom1602 Fin15AnchoredAtom1686 Fin15AnchoredAtom4437 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11312
  ] at hbad
  tauto

theorem fin15Anchored_clause26734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4438 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom4438 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19504
  ] at hbad
  tauto

theorem fin15Anchored_clause26735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4438 chi ∧
      ¬Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1687 Fin15AnchoredAtom4438 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19504
  ] at hbad
  tauto

theorem fin15Anchored_clause26736 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom4439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13360
  ] at hbad
  tauto

theorem fin15Anchored_clause26737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom4439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13360
  ] at hbad
  tauto

theorem fin15Anchored_clause26738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom4439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13360
  ] at hbad
  tauto

theorem fin15Anchored_clause26739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom4439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13360
  ] at hbad
  tauto

theorem fin15Anchored_clause26740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4439 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom4439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13360
  ] at hbad
  tauto

theorem fin15Anchored_clause26741 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom1519 Fin15AnchoredAtom1524
    Fin15AnchoredAtom1604 Fin15AnchoredAtom1688 Fin15AnchoredAtom4439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13360
  ] at hbad
  tauto

theorem fin15Anchored_clause26742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom4440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21552
  ] at hbad
  tauto

theorem fin15Anchored_clause26743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom4440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21552
  ] at hbad
  tauto

theorem fin15Anchored_clause26744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom4440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21552
  ] at hbad
  tauto

theorem fin15Anchored_clause26745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom4440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21552
  ] at hbad
  tauto

theorem fin15Anchored_clause26746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4440 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom4440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21552
  ] at hbad
  tauto

theorem fin15Anchored_clause26747 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom1520 Fin15AnchoredAtom1525
    Fin15AnchoredAtom1605 Fin15AnchoredAtom1689 Fin15AnchoredAtom4440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21552
  ] at hbad
  tauto

theorem fin15Anchored_clause26748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom4441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25648
  ] at hbad
  tauto

theorem fin15Anchored_clause26749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom4441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25648
  ] at hbad
  tauto

theorem fin15Anchored_clause26750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom4441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25648
  ] at hbad
  tauto

theorem fin15Anchored_clause26751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom4441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25648
  ] at hbad
  tauto

end ErdosSzekeres

end
