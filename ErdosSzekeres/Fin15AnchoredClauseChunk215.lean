module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 215. -/

theorem fin15Anchored_clause27520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom4627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28768
  ] at hbad
  tauto

theorem fin15Anchored_clause27521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom4627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28768
  ] at hbad
  tauto

theorem fin15Anchored_clause27522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom4627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28768
  ] at hbad
  tauto

theorem fin15Anchored_clause27523 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom1637 Fin15AnchoredAtom1638
    Fin15AnchoredAtom1694 Fin15AnchoredAtom1750 Fin15AnchoredAtom4627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28768
  ] at hbad
  tauto

theorem fin15Anchored_clause27524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom4628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01952
  ] at hbad
  tauto

theorem fin15Anchored_clause27525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom4628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01952
  ] at hbad
  tauto

theorem fin15Anchored_clause27526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom4628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01952
  ] at hbad
  tauto

theorem fin15Anchored_clause27527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom4628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01952
  ] at hbad
  tauto

theorem fin15Anchored_clause27528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4628 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom4628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01952
  ] at hbad
  tauto

theorem fin15Anchored_clause27529 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4628 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1640 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom1640 Fin15AnchoredAtom1645
    Fin15AnchoredAtom1660 Fin15AnchoredAtom1751 Fin15AnchoredAtom4628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01952
  ] at hbad
  tauto

theorem fin15Anchored_clause27530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom4630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05024
  ] at hbad
  tauto

theorem fin15Anchored_clause27531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom4630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05024
  ] at hbad
  tauto

theorem fin15Anchored_clause27532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom4630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05024
  ] at hbad
  tauto

theorem fin15Anchored_clause27533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom4630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05024
  ] at hbad
  tauto

theorem fin15Anchored_clause27534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4630 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom4630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05024
  ] at hbad
  tauto

theorem fin15Anchored_clause27535 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4630 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom1642 Fin15AnchoredAtom1647
    Fin15AnchoredAtom1662 Fin15AnchoredAtom1753 Fin15AnchoredAtom4630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05024
  ] at hbad
  tauto

theorem fin15Anchored_clause27536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom4631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09120
  ] at hbad
  tauto

theorem fin15Anchored_clause27537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom4631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09120
  ] at hbad
  tauto

theorem fin15Anchored_clause27538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom4631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09120
  ] at hbad
  tauto

theorem fin15Anchored_clause27539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4631 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom4631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09120
  ] at hbad
  tauto

theorem fin15Anchored_clause27540 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4631 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom1643 Fin15AnchoredAtom1648
    Fin15AnchoredAtom1663 Fin15AnchoredAtom1754 Fin15AnchoredAtom4631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09120
  ] at hbad
  tauto

theorem fin15Anchored_clause27541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom4632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17312
  ] at hbad
  tauto

theorem fin15Anchored_clause27542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1644 Fin15AnchoredAtom4632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17312
  ] at hbad
  tauto

theorem fin15Anchored_clause27543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom4632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17312
  ] at hbad
  tauto

theorem fin15Anchored_clause27544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1664 Fin15AnchoredAtom4632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17312
  ] at hbad
  tauto

theorem fin15Anchored_clause27545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4632 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1755 Fin15AnchoredAtom4632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17312
  ] at hbad
  tauto

theorem fin15Anchored_clause27546 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4632 chi ∧
      Fin15AnchoredAtom1639 chi ∧
      Fin15AnchoredAtom1644 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom1644 Fin15AnchoredAtom1649
    Fin15AnchoredAtom1664 Fin15AnchoredAtom1755 Fin15AnchoredAtom4632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17312
  ] at hbad
  tauto

theorem fin15Anchored_clause27547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom4634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05536
  ] at hbad
  tauto

theorem fin15Anchored_clause27548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom4634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05536
  ] at hbad
  tauto

theorem fin15Anchored_clause27549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom4634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05536
  ] at hbad
  tauto

theorem fin15Anchored_clause27550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom4634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05536
  ] at hbad
  tauto

theorem fin15Anchored_clause27551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4634 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom4634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05536
  ] at hbad
  tauto

theorem fin15Anchored_clause27552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4634 chi ∧
      Fin15AnchoredAtom1640 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom1642 Fin15AnchoredAtom1651
    Fin15AnchoredAtom1666 Fin15AnchoredAtom1757 Fin15AnchoredAtom4634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05536
  ] at hbad
  tauto

theorem fin15Anchored_clause27553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom4635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09632
  ] at hbad
  tauto

theorem fin15Anchored_clause27554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom4635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09632
  ] at hbad
  tauto

theorem fin15Anchored_clause27555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom4635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09632
  ] at hbad
  tauto

theorem fin15Anchored_clause27556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom4635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09632
  ] at hbad
  tauto

theorem fin15Anchored_clause27557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4635 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom4635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09632
  ] at hbad
  tauto

theorem fin15Anchored_clause27558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4635 chi ∧
      Fin15AnchoredAtom1640 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom1643 Fin15AnchoredAtom1652
    Fin15AnchoredAtom1667 Fin15AnchoredAtom1758 Fin15AnchoredAtom4635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09632
  ] at hbad
  tauto

theorem fin15Anchored_clause27559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom4636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17824
  ] at hbad
  tauto

theorem fin15Anchored_clause27560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1644 Fin15AnchoredAtom4636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17824
  ] at hbad
  tauto

theorem fin15Anchored_clause27561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom4636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17824
  ] at hbad
  tauto

theorem fin15Anchored_clause27562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1668 Fin15AnchoredAtom4636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17824
  ] at hbad
  tauto

theorem fin15Anchored_clause27563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4636 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1759 Fin15AnchoredAtom4636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17824
  ] at hbad
  tauto

theorem fin15Anchored_clause27564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom4640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12704
  ] at hbad
  tauto

theorem fin15Anchored_clause27565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom4640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12704
  ] at hbad
  tauto

theorem fin15Anchored_clause27566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom4640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12704
  ] at hbad
  tauto

theorem fin15Anchored_clause27567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom4640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12704
  ] at hbad
  tauto

theorem fin15Anchored_clause27568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4640 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom4640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12704
  ] at hbad
  tauto

theorem fin15Anchored_clause27569 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4640 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom1643 Fin15AnchoredAtom1657
    Fin15AnchoredAtom1672 Fin15AnchoredAtom1763 Fin15AnchoredAtom4640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12704
  ] at hbad
  tauto

theorem fin15Anchored_clause27570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom4641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20896
  ] at hbad
  tauto

theorem fin15Anchored_clause27571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1644 Fin15AnchoredAtom4641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20896
  ] at hbad
  tauto

theorem fin15Anchored_clause27572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom4641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20896
  ] at hbad
  tauto

theorem fin15Anchored_clause27573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1673 Fin15AnchoredAtom4641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20896
  ] at hbad
  tauto

theorem fin15Anchored_clause27574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4641 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1764 Fin15AnchoredAtom4641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20896
  ] at hbad
  tauto

theorem fin15Anchored_clause27575 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4641 chi ∧
      Fin15AnchoredAtom1642 chi ∧
      Fin15AnchoredAtom1644 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom1644 Fin15AnchoredAtom1658
    Fin15AnchoredAtom1673 Fin15AnchoredAtom1764 Fin15AnchoredAtom4641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20896
  ] at hbad
  tauto

theorem fin15Anchored_clause27576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom4642 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24992
  ] at hbad
  tauto

theorem fin15Anchored_clause27577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1644 Fin15AnchoredAtom4642 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24992
  ] at hbad
  tauto

theorem fin15Anchored_clause27578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom4642 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24992
  ] at hbad
  tauto

theorem fin15Anchored_clause27579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1674 Fin15AnchoredAtom4642 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24992
  ] at hbad
  tauto

theorem fin15Anchored_clause27580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4642 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1765 Fin15AnchoredAtom4642 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24992
  ] at hbad
  tauto

theorem fin15Anchored_clause27581 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4642 chi ∧
      Fin15AnchoredAtom1643 chi ∧
      Fin15AnchoredAtom1644 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom1644 Fin15AnchoredAtom1659
    Fin15AnchoredAtom1674 Fin15AnchoredAtom1765 Fin15AnchoredAtom4642 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24992
  ] at hbad
  tauto

theorem fin15Anchored_clause27582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom4643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03744
  ] at hbad
  tauto

theorem fin15Anchored_clause27583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom4643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03744
  ] at hbad
  tauto

theorem fin15Anchored_clause27584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom4643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03744
  ] at hbad
  tauto

theorem fin15Anchored_clause27585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4643 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom4643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03744
  ] at hbad
  tauto

theorem fin15Anchored_clause27586 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4643 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1646 chi ∧
      Fin15AnchoredAtom1650 chi ∧
      Fin15AnchoredAtom1675 chi ∧
      Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom1646 Fin15AnchoredAtom1650
    Fin15AnchoredAtom1675 Fin15AnchoredAtom1766 Fin15AnchoredAtom4643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03744
  ] at hbad
  tauto

theorem fin15Anchored_clause27587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom4644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05792
  ] at hbad
  tauto

theorem fin15Anchored_clause27588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom4644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05792
  ] at hbad
  tauto

theorem fin15Anchored_clause27589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom4644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05792
  ] at hbad
  tauto

theorem fin15Anchored_clause27590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom4644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05792
  ] at hbad
  tauto

theorem fin15Anchored_clause27591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4644 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom4644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05792
  ] at hbad
  tauto

theorem fin15Anchored_clause27592 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom1647 Fin15AnchoredAtom1651
    Fin15AnchoredAtom1676 Fin15AnchoredAtom1767 Fin15AnchoredAtom4644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05792
  ] at hbad
  tauto

theorem fin15Anchored_clause27593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom4645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09888
  ] at hbad
  tauto

theorem fin15Anchored_clause27594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom4645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09888
  ] at hbad
  tauto

theorem fin15Anchored_clause27595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom4645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09888
  ] at hbad
  tauto

theorem fin15Anchored_clause27596 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom4645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09888
  ] at hbad
  tauto

theorem fin15Anchored_clause27597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4645 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom4645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09888
  ] at hbad
  tauto

theorem fin15Anchored_clause27598 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4645 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom1648 Fin15AnchoredAtom1652
    Fin15AnchoredAtom1677 Fin15AnchoredAtom1768 Fin15AnchoredAtom4645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09888
  ] at hbad
  tauto

theorem fin15Anchored_clause27599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom4646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18080
  ] at hbad
  tauto

theorem fin15Anchored_clause27600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom4646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18080
  ] at hbad
  tauto

theorem fin15Anchored_clause27601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom4646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18080
  ] at hbad
  tauto

theorem fin15Anchored_clause27602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom4646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18080
  ] at hbad
  tauto

theorem fin15Anchored_clause27603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4646 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom4646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18080
  ] at hbad
  tauto

theorem fin15Anchored_clause27604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4646 chi ∧
      Fin15AnchoredAtom1645 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1653 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom1649 Fin15AnchoredAtom1653
    Fin15AnchoredAtom1678 Fin15AnchoredAtom1769 Fin15AnchoredAtom4646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18080
  ] at hbad
  tauto

theorem fin15Anchored_clause27605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom4647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06816
  ] at hbad
  tauto

theorem fin15Anchored_clause27606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1679 Fin15AnchoredAtom4647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06816
  ] at hbad
  tauto

theorem fin15Anchored_clause27607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4647 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1770 Fin15AnchoredAtom4647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06816
  ] at hbad
  tauto

theorem fin15Anchored_clause27608 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4647 chi ∧
      Fin15AnchoredAtom1646 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1654 chi ∧
      Fin15AnchoredAtom1679 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1646 Fin15AnchoredAtom1647 Fin15AnchoredAtom1654
    Fin15AnchoredAtom1679 Fin15AnchoredAtom1770 Fin15AnchoredAtom4647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06816
  ] at hbad
  tauto

theorem fin15Anchored_clause27609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1646 Fin15AnchoredAtom4648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10912
  ] at hbad
  tauto

theorem fin15Anchored_clause27610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom4648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10912
  ] at hbad
  tauto

theorem fin15Anchored_clause27611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1680 Fin15AnchoredAtom4648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10912
  ] at hbad
  tauto

theorem fin15Anchored_clause27612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4648 chi ∧
      ¬Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1771 Fin15AnchoredAtom4648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10912
  ] at hbad
  tauto

theorem fin15Anchored_clause27613 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4648 chi ∧
      Fin15AnchoredAtom1646 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1655 chi ∧
      Fin15AnchoredAtom1680 chi ∧
      Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1646 Fin15AnchoredAtom1648 Fin15AnchoredAtom1655
    Fin15AnchoredAtom1680 Fin15AnchoredAtom1771 Fin15AnchoredAtom4648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10912
  ] at hbad
  tauto

theorem fin15Anchored_clause27614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4649 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom4649 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19104
  ] at hbad
  tauto

theorem fin15Anchored_clause27615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom4650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12960
  ] at hbad
  tauto

theorem fin15Anchored_clause27616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom4650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12960
  ] at hbad
  tauto

theorem fin15Anchored_clause27617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom4650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12960
  ] at hbad
  tauto

theorem fin15Anchored_clause27618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom4650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12960
  ] at hbad
  tauto

theorem fin15Anchored_clause27619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4650 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom4650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12960
  ] at hbad
  tauto

theorem fin15Anchored_clause27620 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4650 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom1648 Fin15AnchoredAtom1657
    Fin15AnchoredAtom1682 Fin15AnchoredAtom1773 Fin15AnchoredAtom4650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12960
  ] at hbad
  tauto

theorem fin15Anchored_clause27621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom4651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21152
  ] at hbad
  tauto

theorem fin15Anchored_clause27622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom4651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21152
  ] at hbad
  tauto

theorem fin15Anchored_clause27623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom4651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21152
  ] at hbad
  tauto

theorem fin15Anchored_clause27624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom4651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21152
  ] at hbad
  tauto

theorem fin15Anchored_clause27625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4651 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom4651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21152
  ] at hbad
  tauto

theorem fin15Anchored_clause27626 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4651 chi ∧
      Fin15AnchoredAtom1647 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom1649 Fin15AnchoredAtom1658
    Fin15AnchoredAtom1683 Fin15AnchoredAtom1774 Fin15AnchoredAtom4651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21152
  ] at hbad
  tauto

theorem fin15Anchored_clause27627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom4652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25248
  ] at hbad
  tauto

theorem fin15Anchored_clause27628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom4652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25248
  ] at hbad
  tauto

theorem fin15Anchored_clause27629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom4652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25248
  ] at hbad
  tauto

theorem fin15Anchored_clause27630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom4652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25248
  ] at hbad
  tauto

theorem fin15Anchored_clause27631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4652 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom4652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25248
  ] at hbad
  tauto

theorem fin15Anchored_clause27632 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4652 chi ∧
      Fin15AnchoredAtom1648 chi ∧
      Fin15AnchoredAtom1649 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom1649 Fin15AnchoredAtom1659
    Fin15AnchoredAtom1684 Fin15AnchoredAtom1775 Fin15AnchoredAtom4652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25248
  ] at hbad
  tauto

theorem fin15Anchored_clause27633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom4653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07328
  ] at hbad
  tauto

theorem fin15Anchored_clause27634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom4653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07328
  ] at hbad
  tauto

theorem fin15Anchored_clause27635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1685 Fin15AnchoredAtom4653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07328
  ] at hbad
  tauto

theorem fin15Anchored_clause27636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4653 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom4653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07328
  ] at hbad
  tauto

theorem fin15Anchored_clause27637 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4653 chi ∧
      Fin15AnchoredAtom1650 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1654 chi ∧
      Fin15AnchoredAtom1685 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom1651 Fin15AnchoredAtom1654
    Fin15AnchoredAtom1685 Fin15AnchoredAtom1776 Fin15AnchoredAtom4653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07328
  ] at hbad
  tauto

theorem fin15Anchored_clause27638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom4654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11424
  ] at hbad
  tauto

theorem fin15Anchored_clause27639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom4654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11424
  ] at hbad
  tauto

theorem fin15Anchored_clause27640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4654 chi ∧
      ¬Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1686 Fin15AnchoredAtom4654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11424
  ] at hbad
  tauto

theorem fin15Anchored_clause27641 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4654 chi ∧
      Fin15AnchoredAtom1650 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1655 chi ∧
      Fin15AnchoredAtom1686 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom1652 Fin15AnchoredAtom1655
    Fin15AnchoredAtom1686 Fin15AnchoredAtom1777 Fin15AnchoredAtom4654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11424
  ] at hbad
  tauto

theorem fin15Anchored_clause27642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4655 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom4655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19616
  ] at hbad
  tauto

theorem fin15Anchored_clause27643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4655 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom4655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19616
  ] at hbad
  tauto

theorem fin15Anchored_clause27644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom4656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13472
  ] at hbad
  tauto

theorem fin15Anchored_clause27645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom4656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13472
  ] at hbad
  tauto

theorem fin15Anchored_clause27646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom4656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13472
  ] at hbad
  tauto

theorem fin15Anchored_clause27647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom4656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13472
  ] at hbad
  tauto

end ErdosSzekeres

end
