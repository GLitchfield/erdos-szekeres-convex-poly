module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 217. -/

theorem fin15Anchored_clause27776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1816 Fin15AnchoredAtom4693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15392
  ] at hbad
  tauto

theorem fin15Anchored_clause27777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4693 chi ∧
      Fin15AnchoredAtom1685 chi ∧
      Fin15AnchoredAtom1686 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1691 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1685 Fin15AnchoredAtom1686 Fin15AnchoredAtom1688
    Fin15AnchoredAtom1691 Fin15AnchoredAtom1816 Fin15AnchoredAtom4693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15392
  ] at hbad
  tauto

theorem fin15Anchored_clause27778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4694 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1685 Fin15AnchoredAtom4694 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23584
  ] at hbad
  tauto

theorem fin15Anchored_clause27779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4694 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom4694 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23584
  ] at hbad
  tauto

theorem fin15Anchored_clause27780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4695 chi ∧
      ¬Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1818 Fin15AnchoredAtom4695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27680
  ] at hbad
  tauto

theorem fin15Anchored_clause27781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom4696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29728
  ] at hbad
  tauto

theorem fin15Anchored_clause27782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom4696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29728
  ] at hbad
  tauto

theorem fin15Anchored_clause27783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom4696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29728
  ] at hbad
  tauto

theorem fin15Anchored_clause27784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom4696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29728
  ] at hbad
  tauto

theorem fin15Anchored_clause27785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4696 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom4696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29728
  ] at hbad
  tauto

theorem fin15Anchored_clause27786 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom1689 Fin15AnchoredAtom1690
    Fin15AnchoredAtom1694 Fin15AnchoredAtom1819 Fin15AnchoredAtom4696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29728
  ] at hbad
  tauto

theorem fin15Anchored_clause27787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4697 chi ∧
      ¬Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1692 Fin15AnchoredAtom4697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30752
  ] at hbad
  tauto

theorem fin15Anchored_clause27788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4697 chi ∧
      ¬Fin15AnchoredAtom1820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1820 Fin15AnchoredAtom4697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30752
  ] at hbad
  tauto

theorem fin15Anchored_clause27789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom4698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01984
  ] at hbad
  tauto

theorem fin15Anchored_clause27790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom4698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01984
  ] at hbad
  tauto

theorem fin15Anchored_clause27791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom4698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01984
  ] at hbad
  tauto

theorem fin15Anchored_clause27792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom4698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01984
  ] at hbad
  tauto

theorem fin15Anchored_clause27793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4698 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom4698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01984
  ] at hbad
  tauto

theorem fin15Anchored_clause27794 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4698 chi ∧
      Fin15AnchoredAtom1695 chi ∧
      Fin15AnchoredAtom1696 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1716 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom1696 Fin15AnchoredAtom1701
    Fin15AnchoredAtom1716 Fin15AnchoredAtom1751 Fin15AnchoredAtom4698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01984
  ] at hbad
  tauto

theorem fin15Anchored_clause27795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom4700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05056
  ] at hbad
  tauto

theorem fin15Anchored_clause27796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom4700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05056
  ] at hbad
  tauto

theorem fin15Anchored_clause27797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom4700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05056
  ] at hbad
  tauto

theorem fin15Anchored_clause27798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom4700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05056
  ] at hbad
  tauto

theorem fin15Anchored_clause27799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4700 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom4700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05056
  ] at hbad
  tauto

theorem fin15Anchored_clause27800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4700 chi ∧
      Fin15AnchoredAtom1695 chi ∧
      Fin15AnchoredAtom1698 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1718 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom1698 Fin15AnchoredAtom1703
    Fin15AnchoredAtom1718 Fin15AnchoredAtom1753 Fin15AnchoredAtom4700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05056
  ] at hbad
  tauto

theorem fin15Anchored_clause27801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom4701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09152
  ] at hbad
  tauto

theorem fin15Anchored_clause27802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom4701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09152
  ] at hbad
  tauto

theorem fin15Anchored_clause27803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom4701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09152
  ] at hbad
  tauto

theorem fin15Anchored_clause27804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom4701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09152
  ] at hbad
  tauto

theorem fin15Anchored_clause27805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4701 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom4701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09152
  ] at hbad
  tauto

theorem fin15Anchored_clause27806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4701 chi ∧
      Fin15AnchoredAtom1695 chi ∧
      Fin15AnchoredAtom1699 chi ∧
      Fin15AnchoredAtom1704 chi ∧
      Fin15AnchoredAtom1719 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom1699 Fin15AnchoredAtom1704
    Fin15AnchoredAtom1719 Fin15AnchoredAtom1754 Fin15AnchoredAtom4701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09152
  ] at hbad
  tauto

theorem fin15Anchored_clause27807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom4702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17344
  ] at hbad
  tauto

theorem fin15Anchored_clause27808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1700 Fin15AnchoredAtom4702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17344
  ] at hbad
  tauto

theorem fin15Anchored_clause27809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom4702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17344
  ] at hbad
  tauto

theorem fin15Anchored_clause27810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1720 Fin15AnchoredAtom4702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17344
  ] at hbad
  tauto

theorem fin15Anchored_clause27811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4702 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1755 Fin15AnchoredAtom4702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17344
  ] at hbad
  tauto

theorem fin15Anchored_clause27812 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4702 chi ∧
      Fin15AnchoredAtom1695 chi ∧
      Fin15AnchoredAtom1700 chi ∧
      Fin15AnchoredAtom1705 chi ∧
      Fin15AnchoredAtom1720 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom1700 Fin15AnchoredAtom1705
    Fin15AnchoredAtom1720 Fin15AnchoredAtom1755 Fin15AnchoredAtom4702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17344
  ] at hbad
  tauto

theorem fin15Anchored_clause27813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom4704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05568
  ] at hbad
  tauto

theorem fin15Anchored_clause27814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom4704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05568
  ] at hbad
  tauto

theorem fin15Anchored_clause27815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom4704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05568
  ] at hbad
  tauto

theorem fin15Anchored_clause27816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom4704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05568
  ] at hbad
  tauto

theorem fin15Anchored_clause27817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4704 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom4704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05568
  ] at hbad
  tauto

theorem fin15Anchored_clause27818 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4704 chi ∧
      Fin15AnchoredAtom1696 chi ∧
      Fin15AnchoredAtom1698 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1722 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom1698 Fin15AnchoredAtom1707
    Fin15AnchoredAtom1722 Fin15AnchoredAtom1757 Fin15AnchoredAtom4704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05568
  ] at hbad
  tauto

theorem fin15Anchored_clause27819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom4705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09664
  ] at hbad
  tauto

theorem fin15Anchored_clause27820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom4705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09664
  ] at hbad
  tauto

theorem fin15Anchored_clause27821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom4705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09664
  ] at hbad
  tauto

theorem fin15Anchored_clause27822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1723 Fin15AnchoredAtom4705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09664
  ] at hbad
  tauto

theorem fin15Anchored_clause27823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4705 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom4705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09664
  ] at hbad
  tauto

theorem fin15Anchored_clause27824 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4705 chi ∧
      Fin15AnchoredAtom1696 chi ∧
      Fin15AnchoredAtom1699 chi ∧
      Fin15AnchoredAtom1708 chi ∧
      Fin15AnchoredAtom1723 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom1699 Fin15AnchoredAtom1708
    Fin15AnchoredAtom1723 Fin15AnchoredAtom1758 Fin15AnchoredAtom4705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09664
  ] at hbad
  tauto

theorem fin15Anchored_clause27825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom4706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17856
  ] at hbad
  tauto

theorem fin15Anchored_clause27826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1700 Fin15AnchoredAtom4706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17856
  ] at hbad
  tauto

theorem fin15Anchored_clause27827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom4706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17856
  ] at hbad
  tauto

theorem fin15Anchored_clause27828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1724 Fin15AnchoredAtom4706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17856
  ] at hbad
  tauto

theorem fin15Anchored_clause27829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4706 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1759 Fin15AnchoredAtom4706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17856
  ] at hbad
  tauto

theorem fin15Anchored_clause27830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4706 chi ∧
      Fin15AnchoredAtom1696 chi ∧
      Fin15AnchoredAtom1700 chi ∧
      Fin15AnchoredAtom1709 chi ∧
      Fin15AnchoredAtom1724 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom1700 Fin15AnchoredAtom1709
    Fin15AnchoredAtom1724 Fin15AnchoredAtom1759 Fin15AnchoredAtom4706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17856
  ] at hbad
  tauto

theorem fin15Anchored_clause27831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom4710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12736
  ] at hbad
  tauto

theorem fin15Anchored_clause27832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom4710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12736
  ] at hbad
  tauto

theorem fin15Anchored_clause27833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom4710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12736
  ] at hbad
  tauto

theorem fin15Anchored_clause27834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom4710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12736
  ] at hbad
  tauto

theorem fin15Anchored_clause27835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4710 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom4710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12736
  ] at hbad
  tauto

theorem fin15Anchored_clause27836 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4710 chi ∧
      Fin15AnchoredAtom1698 chi ∧
      Fin15AnchoredAtom1699 chi ∧
      Fin15AnchoredAtom1713 chi ∧
      Fin15AnchoredAtom1728 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom1699 Fin15AnchoredAtom1713
    Fin15AnchoredAtom1728 Fin15AnchoredAtom1763 Fin15AnchoredAtom4710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12736
  ] at hbad
  tauto

theorem fin15Anchored_clause27837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom4711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20928
  ] at hbad
  tauto

theorem fin15Anchored_clause27838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1700 Fin15AnchoredAtom4711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20928
  ] at hbad
  tauto

theorem fin15Anchored_clause27839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom4711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20928
  ] at hbad
  tauto

theorem fin15Anchored_clause27840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1729 Fin15AnchoredAtom4711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20928
  ] at hbad
  tauto

theorem fin15Anchored_clause27841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4711 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1764 Fin15AnchoredAtom4711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20928
  ] at hbad
  tauto

theorem fin15Anchored_clause27842 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4711 chi ∧
      Fin15AnchoredAtom1698 chi ∧
      Fin15AnchoredAtom1700 chi ∧
      Fin15AnchoredAtom1714 chi ∧
      Fin15AnchoredAtom1729 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom1700 Fin15AnchoredAtom1714
    Fin15AnchoredAtom1729 Fin15AnchoredAtom1764 Fin15AnchoredAtom4711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20928
  ] at hbad
  tauto

theorem fin15Anchored_clause27843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom4712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25024
  ] at hbad
  tauto

theorem fin15Anchored_clause27844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1700 Fin15AnchoredAtom4712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25024
  ] at hbad
  tauto

theorem fin15Anchored_clause27845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom4712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25024
  ] at hbad
  tauto

theorem fin15Anchored_clause27846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1730 Fin15AnchoredAtom4712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25024
  ] at hbad
  tauto

theorem fin15Anchored_clause27847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4712 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1765 Fin15AnchoredAtom4712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25024
  ] at hbad
  tauto

theorem fin15Anchored_clause27848 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4712 chi ∧
      Fin15AnchoredAtom1699 chi ∧
      Fin15AnchoredAtom1700 chi ∧
      Fin15AnchoredAtom1715 chi ∧
      Fin15AnchoredAtom1730 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom1700 Fin15AnchoredAtom1715
    Fin15AnchoredAtom1730 Fin15AnchoredAtom1765 Fin15AnchoredAtom4712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25024
  ] at hbad
  tauto

theorem fin15Anchored_clause27849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom4713 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03776
  ] at hbad
  tauto

theorem fin15Anchored_clause27850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1702 Fin15AnchoredAtom4713 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03776
  ] at hbad
  tauto

theorem fin15Anchored_clause27851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1731 Fin15AnchoredAtom4713 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03776
  ] at hbad
  tauto

theorem fin15Anchored_clause27852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4713 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom4713 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03776
  ] at hbad
  tauto

theorem fin15Anchored_clause27853 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4713 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1702 chi ∧
      Fin15AnchoredAtom1706 chi ∧
      Fin15AnchoredAtom1731 chi ∧
      Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom1702 Fin15AnchoredAtom1706
    Fin15AnchoredAtom1731 Fin15AnchoredAtom1766 Fin15AnchoredAtom4713 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03776
  ] at hbad
  tauto

theorem fin15Anchored_clause27854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom4714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05824
  ] at hbad
  tauto

theorem fin15Anchored_clause27855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom4714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05824
  ] at hbad
  tauto

theorem fin15Anchored_clause27856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom4714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05824
  ] at hbad
  tauto

theorem fin15Anchored_clause27857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom4714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05824
  ] at hbad
  tauto

theorem fin15Anchored_clause27858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4714 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom4714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05824
  ] at hbad
  tauto

theorem fin15Anchored_clause27859 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom1703 Fin15AnchoredAtom1707
    Fin15AnchoredAtom1732 Fin15AnchoredAtom1767 Fin15AnchoredAtom4714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05824
  ] at hbad
  tauto

theorem fin15Anchored_clause27860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom4715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09920
  ] at hbad
  tauto

theorem fin15Anchored_clause27861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom4715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09920
  ] at hbad
  tauto

theorem fin15Anchored_clause27862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom4715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09920
  ] at hbad
  tauto

theorem fin15Anchored_clause27863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom4715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09920
  ] at hbad
  tauto

theorem fin15Anchored_clause27864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4715 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom4715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09920
  ] at hbad
  tauto

theorem fin15Anchored_clause27865 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4715 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1704 chi ∧
      Fin15AnchoredAtom1708 chi ∧
      Fin15AnchoredAtom1733 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom1704 Fin15AnchoredAtom1708
    Fin15AnchoredAtom1733 Fin15AnchoredAtom1768 Fin15AnchoredAtom4715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09920
  ] at hbad
  tauto

theorem fin15Anchored_clause27866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom4716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18112
  ] at hbad
  tauto

theorem fin15Anchored_clause27867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom4716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18112
  ] at hbad
  tauto

theorem fin15Anchored_clause27868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom4716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18112
  ] at hbad
  tauto

theorem fin15Anchored_clause27869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom4716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18112
  ] at hbad
  tauto

theorem fin15Anchored_clause27870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4716 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom4716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18112
  ] at hbad
  tauto

theorem fin15Anchored_clause27871 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4716 chi ∧
      Fin15AnchoredAtom1701 chi ∧
      Fin15AnchoredAtom1705 chi ∧
      Fin15AnchoredAtom1709 chi ∧
      Fin15AnchoredAtom1734 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom1705 Fin15AnchoredAtom1709
    Fin15AnchoredAtom1734 Fin15AnchoredAtom1769 Fin15AnchoredAtom4716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18112
  ] at hbad
  tauto

theorem fin15Anchored_clause27872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom4717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06848
  ] at hbad
  tauto

theorem fin15Anchored_clause27873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1710 Fin15AnchoredAtom4717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06848
  ] at hbad
  tauto

theorem fin15Anchored_clause27874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom4717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06848
  ] at hbad
  tauto

theorem fin15Anchored_clause27875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4717 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1770 Fin15AnchoredAtom4717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06848
  ] at hbad
  tauto

theorem fin15Anchored_clause27876 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4717 chi ∧
      Fin15AnchoredAtom1702 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1710 chi ∧
      Fin15AnchoredAtom1735 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1702 Fin15AnchoredAtom1703 Fin15AnchoredAtom1710
    Fin15AnchoredAtom1735 Fin15AnchoredAtom1770 Fin15AnchoredAtom4717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06848
  ] at hbad
  tauto

theorem fin15Anchored_clause27877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4718 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom4718 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10944
  ] at hbad
  tauto

theorem fin15Anchored_clause27878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4718 chi ∧
      ¬Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1736 Fin15AnchoredAtom4718 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10944
  ] at hbad
  tauto

theorem fin15Anchored_clause27879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4719 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom4719 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19136
  ] at hbad
  tauto

theorem fin15Anchored_clause27880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom4720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12992
  ] at hbad
  tauto

theorem fin15Anchored_clause27881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom4720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12992
  ] at hbad
  tauto

theorem fin15Anchored_clause27882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom4720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12992
  ] at hbad
  tauto

theorem fin15Anchored_clause27883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom4720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12992
  ] at hbad
  tauto

theorem fin15Anchored_clause27884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4720 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom4720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12992
  ] at hbad
  tauto

theorem fin15Anchored_clause27885 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4720 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1704 chi ∧
      Fin15AnchoredAtom1713 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom1704 Fin15AnchoredAtom1713
    Fin15AnchoredAtom1738 Fin15AnchoredAtom1773 Fin15AnchoredAtom4720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12992
  ] at hbad
  tauto

theorem fin15Anchored_clause27886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom4721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21184
  ] at hbad
  tauto

theorem fin15Anchored_clause27887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom4721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21184
  ] at hbad
  tauto

theorem fin15Anchored_clause27888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom4721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21184
  ] at hbad
  tauto

theorem fin15Anchored_clause27889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom4721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21184
  ] at hbad
  tauto

theorem fin15Anchored_clause27890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4721 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom4721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21184
  ] at hbad
  tauto

theorem fin15Anchored_clause27891 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4721 chi ∧
      Fin15AnchoredAtom1703 chi ∧
      Fin15AnchoredAtom1705 chi ∧
      Fin15AnchoredAtom1714 chi ∧
      Fin15AnchoredAtom1739 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom1705 Fin15AnchoredAtom1714
    Fin15AnchoredAtom1739 Fin15AnchoredAtom1774 Fin15AnchoredAtom4721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21184
  ] at hbad
  tauto

theorem fin15Anchored_clause27892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom4722 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25280
  ] at hbad
  tauto

theorem fin15Anchored_clause27893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom4722 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25280
  ] at hbad
  tauto

theorem fin15Anchored_clause27894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom4722 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25280
  ] at hbad
  tauto

theorem fin15Anchored_clause27895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom4722 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25280
  ] at hbad
  tauto

theorem fin15Anchored_clause27896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4722 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom4722 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25280
  ] at hbad
  tauto

theorem fin15Anchored_clause27897 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4722 chi ∧
      Fin15AnchoredAtom1704 chi ∧
      Fin15AnchoredAtom1705 chi ∧
      Fin15AnchoredAtom1715 chi ∧
      Fin15AnchoredAtom1740 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom1705 Fin15AnchoredAtom1715
    Fin15AnchoredAtom1740 Fin15AnchoredAtom1775 Fin15AnchoredAtom4722 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25280
  ] at hbad
  tauto

theorem fin15Anchored_clause27898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1706 Fin15AnchoredAtom4723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07360
  ] at hbad
  tauto

theorem fin15Anchored_clause27899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom4723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07360
  ] at hbad
  tauto

theorem fin15Anchored_clause27900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1741 Fin15AnchoredAtom4723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07360
  ] at hbad
  tauto

theorem fin15Anchored_clause27901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4723 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom4723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07360
  ] at hbad
  tauto

theorem fin15Anchored_clause27902 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4723 chi ∧
      Fin15AnchoredAtom1706 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1710 chi ∧
      Fin15AnchoredAtom1741 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1706 Fin15AnchoredAtom1707 Fin15AnchoredAtom1710
    Fin15AnchoredAtom1741 Fin15AnchoredAtom1776 Fin15AnchoredAtom4723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07360
  ] at hbad
  tauto

theorem fin15Anchored_clause27903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1706 Fin15AnchoredAtom4724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11456
  ] at hbad
  tauto

end ErdosSzekeres

end
