module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 209. -/

theorem fin15Anchored_clause26752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4441 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom4441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25648
  ] at hbad
  tauto

theorem fin15Anchored_clause26753 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom1520 Fin15AnchoredAtom1526
    Fin15AnchoredAtom1606 Fin15AnchoredAtom1690 Fin15AnchoredAtom4441 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25648
  ] at hbad
  tauto

theorem fin15Anchored_clause26754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1607 Fin15AnchoredAtom4442 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14384
  ] at hbad
  tauto

theorem fin15Anchored_clause26755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4442 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1691 Fin15AnchoredAtom4442 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14384
  ] at hbad
  tauto

theorem fin15Anchored_clause26756 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4442 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1522 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1607 chi ∧
      Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1521 Fin15AnchoredAtom1522 Fin15AnchoredAtom1524
    Fin15AnchoredAtom1607 Fin15AnchoredAtom1691 Fin15AnchoredAtom4442 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14384
  ] at hbad
  tauto

theorem fin15Anchored_clause26757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4443 chi ∧
      ¬Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1692 Fin15AnchoredAtom4443 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22576
  ] at hbad
  tauto

theorem fin15Anchored_clause26758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom4445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28720
  ] at hbad
  tauto

theorem fin15Anchored_clause26759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom4445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28720
  ] at hbad
  tauto

theorem fin15Anchored_clause26760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom4445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28720
  ] at hbad
  tauto

theorem fin15Anchored_clause26761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom4445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28720
  ] at hbad
  tauto

theorem fin15Anchored_clause26762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4445 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom4445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28720
  ] at hbad
  tauto

theorem fin15Anchored_clause26763 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom1525 Fin15AnchoredAtom1526
    Fin15AnchoredAtom1610 Fin15AnchoredAtom1694 Fin15AnchoredAtom4445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28720
  ] at hbad
  tauto

theorem fin15Anchored_clause26764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom4446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00976
  ] at hbad
  tauto

theorem fin15Anchored_clause26765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom4446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00976
  ] at hbad
  tauto

theorem fin15Anchored_clause26766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom4446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00976
  ] at hbad
  tauto

theorem fin15Anchored_clause26767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom4446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00976
  ] at hbad
  tauto

theorem fin15Anchored_clause26768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4446 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom4446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00976
  ] at hbad
  tauto

theorem fin15Anchored_clause26769 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4446 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom1528 Fin15AnchoredAtom1534
    Fin15AnchoredAtom1555 Fin15AnchoredAtom1695 Fin15AnchoredAtom4446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00976
  ] at hbad
  tauto

theorem fin15Anchored_clause26770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom4447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01488
  ] at hbad
  tauto

theorem fin15Anchored_clause26771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom4447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01488
  ] at hbad
  tauto

theorem fin15Anchored_clause26772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom4447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01488
  ] at hbad
  tauto

theorem fin15Anchored_clause26773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom4447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01488
  ] at hbad
  tauto

theorem fin15Anchored_clause26774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4447 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom4447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01488
  ] at hbad
  tauto

theorem fin15Anchored_clause26775 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4447 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom1529 Fin15AnchoredAtom1535
    Fin15AnchoredAtom1556 Fin15AnchoredAtom1696 Fin15AnchoredAtom4447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01488
  ] at hbad
  tauto

theorem fin15Anchored_clause26776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom4449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04560
  ] at hbad
  tauto

theorem fin15Anchored_clause26777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom4449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04560
  ] at hbad
  tauto

theorem fin15Anchored_clause26778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom4449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04560
  ] at hbad
  tauto

theorem fin15Anchored_clause26779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom4449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04560
  ] at hbad
  tauto

theorem fin15Anchored_clause26780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4449 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom4449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04560
  ] at hbad
  tauto

theorem fin15Anchored_clause26781 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4449 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom1531 Fin15AnchoredAtom1537
    Fin15AnchoredAtom1558 Fin15AnchoredAtom1698 Fin15AnchoredAtom4449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04560
  ] at hbad
  tauto

theorem fin15Anchored_clause26782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom4450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08656
  ] at hbad
  tauto

theorem fin15Anchored_clause26783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom4450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08656
  ] at hbad
  tauto

theorem fin15Anchored_clause26784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom4450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08656
  ] at hbad
  tauto

theorem fin15Anchored_clause26785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4450 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom4450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08656
  ] at hbad
  tauto

theorem fin15Anchored_clause26786 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4450 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom1532 Fin15AnchoredAtom1538
    Fin15AnchoredAtom1559 Fin15AnchoredAtom1699 Fin15AnchoredAtom4450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08656
  ] at hbad
  tauto

theorem fin15Anchored_clause26787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom4451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16848
  ] at hbad
  tauto

theorem fin15Anchored_clause26788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom4451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16848
  ] at hbad
  tauto

theorem fin15Anchored_clause26789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1539 Fin15AnchoredAtom4451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16848
  ] at hbad
  tauto

theorem fin15Anchored_clause26790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom4451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16848
  ] at hbad
  tauto

theorem fin15Anchored_clause26791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4451 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1700 Fin15AnchoredAtom4451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16848
  ] at hbad
  tauto

theorem fin15Anchored_clause26792 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4451 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom1533 Fin15AnchoredAtom1539
    Fin15AnchoredAtom1560 Fin15AnchoredAtom1700 Fin15AnchoredAtom4451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16848
  ] at hbad
  tauto

theorem fin15Anchored_clause26793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom4452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01744
  ] at hbad
  tauto

theorem fin15Anchored_clause26794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom4452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01744
  ] at hbad
  tauto

theorem fin15Anchored_clause26795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom4452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01744
  ] at hbad
  tauto

theorem fin15Anchored_clause26796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom4452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01744
  ] at hbad
  tauto

theorem fin15Anchored_clause26797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4452 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom4452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01744
  ] at hbad
  tauto

theorem fin15Anchored_clause26798 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom1529 Fin15AnchoredAtom1540
    Fin15AnchoredAtom1561 Fin15AnchoredAtom1701 Fin15AnchoredAtom4452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01744
  ] at hbad
  tauto

theorem fin15Anchored_clause26799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom4453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02768
  ] at hbad
  tauto

theorem fin15Anchored_clause26800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1530 Fin15AnchoredAtom4453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02768
  ] at hbad
  tauto

theorem fin15Anchored_clause26801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1541 Fin15AnchoredAtom4453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02768
  ] at hbad
  tauto

theorem fin15Anchored_clause26802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4453 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1562 Fin15AnchoredAtom4453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02768
  ] at hbad
  tauto

theorem fin15Anchored_clause26803 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4453 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1530 chi ∧
      Fin15AnchoredAtom1541 chi ∧
      Fin15AnchoredAtom1562 chi ∧
      Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom1530 Fin15AnchoredAtom1541
    Fin15AnchoredAtom1562 Fin15AnchoredAtom1702 Fin15AnchoredAtom4453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02768
  ] at hbad
  tauto

theorem fin15Anchored_clause26804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom4454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04816
  ] at hbad
  tauto

theorem fin15Anchored_clause26805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom4454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04816
  ] at hbad
  tauto

theorem fin15Anchored_clause26806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom4454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04816
  ] at hbad
  tauto

theorem fin15Anchored_clause26807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom4454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04816
  ] at hbad
  tauto

theorem fin15Anchored_clause26808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4454 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom4454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04816
  ] at hbad
  tauto

theorem fin15Anchored_clause26809 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom1531 Fin15AnchoredAtom1542
    Fin15AnchoredAtom1563 Fin15AnchoredAtom1703 Fin15AnchoredAtom4454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04816
  ] at hbad
  tauto

theorem fin15Anchored_clause26810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom4455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08912
  ] at hbad
  tauto

theorem fin15Anchored_clause26811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom4455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08912
  ] at hbad
  tauto

theorem fin15Anchored_clause26812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom4455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08912
  ] at hbad
  tauto

theorem fin15Anchored_clause26813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom4455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08912
  ] at hbad
  tauto

theorem fin15Anchored_clause26814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4455 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom4455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08912
  ] at hbad
  tauto

theorem fin15Anchored_clause26815 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom1532 Fin15AnchoredAtom1543
    Fin15AnchoredAtom1564 Fin15AnchoredAtom1704 Fin15AnchoredAtom4455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08912
  ] at hbad
  tauto

theorem fin15Anchored_clause26816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom4456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17104
  ] at hbad
  tauto

theorem fin15Anchored_clause26817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom4456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17104
  ] at hbad
  tauto

theorem fin15Anchored_clause26818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom4456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17104
  ] at hbad
  tauto

theorem fin15Anchored_clause26819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom4456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17104
  ] at hbad
  tauto

theorem fin15Anchored_clause26820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4456 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom4456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17104
  ] at hbad
  tauto

theorem fin15Anchored_clause26821 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom1533 Fin15AnchoredAtom1544
    Fin15AnchoredAtom1565 Fin15AnchoredAtom1705 Fin15AnchoredAtom4456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17104
  ] at hbad
  tauto

theorem fin15Anchored_clause26822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom4457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03280
  ] at hbad
  tauto

theorem fin15Anchored_clause26823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1530 Fin15AnchoredAtom4457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03280
  ] at hbad
  tauto

theorem fin15Anchored_clause26824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4457 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1566 Fin15AnchoredAtom4457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03280
  ] at hbad
  tauto

theorem fin15Anchored_clause26825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom4458 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05328
  ] at hbad
  tauto

theorem fin15Anchored_clause26826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom4458 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05328
  ] at hbad
  tauto

theorem fin15Anchored_clause26827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom4458 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05328
  ] at hbad
  tauto

theorem fin15Anchored_clause26828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom4458 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05328
  ] at hbad
  tauto

theorem fin15Anchored_clause26829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4458 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom4458 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05328
  ] at hbad
  tauto

theorem fin15Anchored_clause26830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom1531 Fin15AnchoredAtom1546
    Fin15AnchoredAtom1567 Fin15AnchoredAtom1707 Fin15AnchoredAtom4458 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05328
  ] at hbad
  tauto

theorem fin15Anchored_clause26831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom4459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09424
  ] at hbad
  tauto

theorem fin15Anchored_clause26832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom4459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09424
  ] at hbad
  tauto

theorem fin15Anchored_clause26833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom4459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09424
  ] at hbad
  tauto

theorem fin15Anchored_clause26834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom4459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09424
  ] at hbad
  tauto

theorem fin15Anchored_clause26835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4459 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom4459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09424
  ] at hbad
  tauto

theorem fin15Anchored_clause26836 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom1532 Fin15AnchoredAtom1547
    Fin15AnchoredAtom1568 Fin15AnchoredAtom1708 Fin15AnchoredAtom4459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09424
  ] at hbad
  tauto

theorem fin15Anchored_clause26837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom4460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17616
  ] at hbad
  tauto

theorem fin15Anchored_clause26838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom4460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17616
  ] at hbad
  tauto

theorem fin15Anchored_clause26839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom4460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17616
  ] at hbad
  tauto

theorem fin15Anchored_clause26840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom4460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17616
  ] at hbad
  tauto

theorem fin15Anchored_clause26841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4460 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom4460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17616
  ] at hbad
  tauto

theorem fin15Anchored_clause26842 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom1533 Fin15AnchoredAtom1548
    Fin15AnchoredAtom1569 Fin15AnchoredAtom1709 Fin15AnchoredAtom4460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17616
  ] at hbad
  tauto

theorem fin15Anchored_clause26843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1530 Fin15AnchoredAtom4461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06352
  ] at hbad
  tauto

theorem fin15Anchored_clause26844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom4461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06352
  ] at hbad
  tauto

theorem fin15Anchored_clause26845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1549 Fin15AnchoredAtom4461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06352
  ] at hbad
  tauto

theorem fin15Anchored_clause26846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4461 chi ∧
      ¬Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1710 Fin15AnchoredAtom4461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06352
  ] at hbad
  tauto

theorem fin15Anchored_clause26847 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4461 chi ∧
      Fin15AnchoredAtom1530 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1549 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1530 Fin15AnchoredAtom1531 Fin15AnchoredAtom1549
    Fin15AnchoredAtom1570 Fin15AnchoredAtom1710 Fin15AnchoredAtom4461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06352
  ] at hbad
  tauto

theorem fin15Anchored_clause26848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4462 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1530 Fin15AnchoredAtom4462 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10448
  ] at hbad
  tauto

theorem fin15Anchored_clause26849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4462 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom4462 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10448
  ] at hbad
  tauto

theorem fin15Anchored_clause26850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4463 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom4463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18640
  ] at hbad
  tauto

theorem fin15Anchored_clause26851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom4464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12496
  ] at hbad
  tauto

theorem fin15Anchored_clause26852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom4464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12496
  ] at hbad
  tauto

theorem fin15Anchored_clause26853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom4464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12496
  ] at hbad
  tauto

theorem fin15Anchored_clause26854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom4464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12496
  ] at hbad
  tauto

theorem fin15Anchored_clause26855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4464 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom4464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12496
  ] at hbad
  tauto

theorem fin15Anchored_clause26856 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom1532 Fin15AnchoredAtom1552
    Fin15AnchoredAtom1573 Fin15AnchoredAtom1713 Fin15AnchoredAtom4464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12496
  ] at hbad
  tauto

theorem fin15Anchored_clause26857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom4465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20688
  ] at hbad
  tauto

theorem fin15Anchored_clause26858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom4465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20688
  ] at hbad
  tauto

theorem fin15Anchored_clause26859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom4465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20688
  ] at hbad
  tauto

theorem fin15Anchored_clause26860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom4465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20688
  ] at hbad
  tauto

theorem fin15Anchored_clause26861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4465 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom4465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20688
  ] at hbad
  tauto

theorem fin15Anchored_clause26862 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom1533 Fin15AnchoredAtom1553
    Fin15AnchoredAtom1574 Fin15AnchoredAtom1714 Fin15AnchoredAtom4465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20688
  ] at hbad
  tauto

theorem fin15Anchored_clause26863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom4466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24784
  ] at hbad
  tauto

theorem fin15Anchored_clause26864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom4466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24784
  ] at hbad
  tauto

theorem fin15Anchored_clause26865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom4466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24784
  ] at hbad
  tauto

theorem fin15Anchored_clause26866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom4466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24784
  ] at hbad
  tauto

theorem fin15Anchored_clause26867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4466 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom4466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24784
  ] at hbad
  tauto

theorem fin15Anchored_clause26868 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom1533 Fin15AnchoredAtom1554
    Fin15AnchoredAtom1575 Fin15AnchoredAtom1715 Fin15AnchoredAtom4466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24784
  ] at hbad
  tauto

theorem fin15Anchored_clause26869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom4467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01872
  ] at hbad
  tauto

theorem fin15Anchored_clause26870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom4467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01872
  ] at hbad
  tauto

theorem fin15Anchored_clause26871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom4467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01872
  ] at hbad
  tauto

theorem fin15Anchored_clause26872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom4467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01872
  ] at hbad
  tauto

theorem fin15Anchored_clause26873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4467 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom4467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01872
  ] at hbad
  tauto

theorem fin15Anchored_clause26874 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4467 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom1535 Fin15AnchoredAtom1540
    Fin15AnchoredAtom1576 Fin15AnchoredAtom1716 Fin15AnchoredAtom4467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01872
  ] at hbad
  tauto

theorem fin15Anchored_clause26875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom4469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04944
  ] at hbad
  tauto

theorem fin15Anchored_clause26876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom4469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04944
  ] at hbad
  tauto

theorem fin15Anchored_clause26877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom4469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04944
  ] at hbad
  tauto

theorem fin15Anchored_clause26878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom4469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04944
  ] at hbad
  tauto

theorem fin15Anchored_clause26879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4469 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom4469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04944
  ] at hbad
  tauto

end ErdosSzekeres

end
