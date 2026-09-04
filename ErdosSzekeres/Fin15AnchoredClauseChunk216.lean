module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 216. -/

theorem fin15Anchored_clause27648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4656 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom4656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13472
  ] at hbad
  tauto

theorem fin15Anchored_clause27649 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4656 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom1652 Fin15AnchoredAtom1657
    Fin15AnchoredAtom1688 Fin15AnchoredAtom1779 Fin15AnchoredAtom4656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13472
  ] at hbad
  tauto

theorem fin15Anchored_clause27650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom4657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21664
  ] at hbad
  tauto

theorem fin15Anchored_clause27651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom4657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21664
  ] at hbad
  tauto

theorem fin15Anchored_clause27652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom4657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21664
  ] at hbad
  tauto

theorem fin15Anchored_clause27653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom4657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21664
  ] at hbad
  tauto

theorem fin15Anchored_clause27654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4657 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom4657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21664
  ] at hbad
  tauto

theorem fin15Anchored_clause27655 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4657 chi ∧
      Fin15AnchoredAtom1651 chi ∧
      Fin15AnchoredAtom1653 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom1653 Fin15AnchoredAtom1658
    Fin15AnchoredAtom1689 Fin15AnchoredAtom1780 Fin15AnchoredAtom4657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21664
  ] at hbad
  tauto

theorem fin15Anchored_clause27656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom4658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25760
  ] at hbad
  tauto

theorem fin15Anchored_clause27657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom4658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25760
  ] at hbad
  tauto

theorem fin15Anchored_clause27658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom4658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25760
  ] at hbad
  tauto

theorem fin15Anchored_clause27659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom4658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25760
  ] at hbad
  tauto

theorem fin15Anchored_clause27660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4658 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom4658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25760
  ] at hbad
  tauto

theorem fin15Anchored_clause27661 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4658 chi ∧
      Fin15AnchoredAtom1652 chi ∧
      Fin15AnchoredAtom1653 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom1653 Fin15AnchoredAtom1659
    Fin15AnchoredAtom1690 Fin15AnchoredAtom1781 Fin15AnchoredAtom4658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25760
  ] at hbad
  tauto

theorem fin15Anchored_clause27662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1654 Fin15AnchoredAtom4659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14496
  ] at hbad
  tauto

theorem fin15Anchored_clause27663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1655 Fin15AnchoredAtom4659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14496
  ] at hbad
  tauto

theorem fin15Anchored_clause27664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom4659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14496
  ] at hbad
  tauto

theorem fin15Anchored_clause27665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1691 Fin15AnchoredAtom4659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14496
  ] at hbad
  tauto

theorem fin15Anchored_clause27666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4659 chi ∧
      ¬Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1782 Fin15AnchoredAtom4659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14496
  ] at hbad
  tauto

theorem fin15Anchored_clause27667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4660 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom4660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22688
  ] at hbad
  tauto

theorem fin15Anchored_clause27668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4660 chi ∧
      ¬Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1692 Fin15AnchoredAtom4660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22688
  ] at hbad
  tauto

theorem fin15Anchored_clause27669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4660 chi ∧
      ¬Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1783 Fin15AnchoredAtom4660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22688
  ] at hbad
  tauto

theorem fin15Anchored_clause27670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4661 chi ∧
      ¬Fin15AnchoredAtom1656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1656 Fin15AnchoredAtom4661 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26784
  ] at hbad
  tauto

theorem fin15Anchored_clause27671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom4662 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28832
  ] at hbad
  tauto

theorem fin15Anchored_clause27672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom4662 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28832
  ] at hbad
  tauto

theorem fin15Anchored_clause27673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom4662 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28832
  ] at hbad
  tauto

theorem fin15Anchored_clause27674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom4662 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28832
  ] at hbad
  tauto

theorem fin15Anchored_clause27675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4662 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom4662 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28832
  ] at hbad
  tauto

theorem fin15Anchored_clause27676 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom1657 chi ∧
      Fin15AnchoredAtom1658 chi ∧
      Fin15AnchoredAtom1659 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom1658 Fin15AnchoredAtom1659
    Fin15AnchoredAtom1694 Fin15AnchoredAtom1785 Fin15AnchoredAtom4662 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28832
  ] at hbad
  tauto

theorem fin15Anchored_clause27677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom4664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05920
  ] at hbad
  tauto

theorem fin15Anchored_clause27678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom4664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05920
  ] at hbad
  tauto

theorem fin15Anchored_clause27679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom4664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05920
  ] at hbad
  tauto

theorem fin15Anchored_clause27680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom4664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05920
  ] at hbad
  tauto

theorem fin15Anchored_clause27681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4664 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom4664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05920
  ] at hbad
  tauto

theorem fin15Anchored_clause27682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom1662 Fin15AnchoredAtom1666
    Fin15AnchoredAtom1676 Fin15AnchoredAtom1787 Fin15AnchoredAtom4664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05920
  ] at hbad
  tauto

theorem fin15Anchored_clause27683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom4665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10016
  ] at hbad
  tauto

theorem fin15Anchored_clause27684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom4665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10016
  ] at hbad
  tauto

theorem fin15Anchored_clause27685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom4665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10016
  ] at hbad
  tauto

theorem fin15Anchored_clause27686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom4665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10016
  ] at hbad
  tauto

theorem fin15Anchored_clause27687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4665 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1788 Fin15AnchoredAtom4665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10016
  ] at hbad
  tauto

theorem fin15Anchored_clause27688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4665 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom1663 Fin15AnchoredAtom1667
    Fin15AnchoredAtom1677 Fin15AnchoredAtom1788 Fin15AnchoredAtom4665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10016
  ] at hbad
  tauto

theorem fin15Anchored_clause27689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom4666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18208
  ] at hbad
  tauto

theorem fin15Anchored_clause27690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1664 Fin15AnchoredAtom4666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18208
  ] at hbad
  tauto

theorem fin15Anchored_clause27691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1668 Fin15AnchoredAtom4666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18208
  ] at hbad
  tauto

theorem fin15Anchored_clause27692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom4666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18208
  ] at hbad
  tauto

theorem fin15Anchored_clause27693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4666 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1789 Fin15AnchoredAtom4666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18208
  ] at hbad
  tauto

theorem fin15Anchored_clause27694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4666 chi ∧
      Fin15AnchoredAtom1660 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1668 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom1664 Fin15AnchoredAtom1668
    Fin15AnchoredAtom1678 Fin15AnchoredAtom1789 Fin15AnchoredAtom4666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18208
  ] at hbad
  tauto

theorem fin15Anchored_clause27695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom4670 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13088
  ] at hbad
  tauto

theorem fin15Anchored_clause27696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom4670 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13088
  ] at hbad
  tauto

theorem fin15Anchored_clause27697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom4670 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13088
  ] at hbad
  tauto

theorem fin15Anchored_clause27698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom4670 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13088
  ] at hbad
  tauto

theorem fin15Anchored_clause27699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4670 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom4670 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13088
  ] at hbad
  tauto

theorem fin15Anchored_clause27700 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4670 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom1663 Fin15AnchoredAtom1672
    Fin15AnchoredAtom1682 Fin15AnchoredAtom1793 Fin15AnchoredAtom4670 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13088
  ] at hbad
  tauto

theorem fin15Anchored_clause27701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom4671 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21280
  ] at hbad
  tauto

theorem fin15Anchored_clause27702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1664 Fin15AnchoredAtom4671 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21280
  ] at hbad
  tauto

theorem fin15Anchored_clause27703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1673 Fin15AnchoredAtom4671 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21280
  ] at hbad
  tauto

theorem fin15Anchored_clause27704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom4671 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21280
  ] at hbad
  tauto

theorem fin15Anchored_clause27705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4671 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1794 Fin15AnchoredAtom4671 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21280
  ] at hbad
  tauto

theorem fin15Anchored_clause27706 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4671 chi ∧
      Fin15AnchoredAtom1662 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom1664 Fin15AnchoredAtom1673
    Fin15AnchoredAtom1683 Fin15AnchoredAtom1794 Fin15AnchoredAtom4671 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21280
  ] at hbad
  tauto

theorem fin15Anchored_clause27707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom4672 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25376
  ] at hbad
  tauto

theorem fin15Anchored_clause27708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1664 Fin15AnchoredAtom4672 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25376
  ] at hbad
  tauto

theorem fin15Anchored_clause27709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1674 Fin15AnchoredAtom4672 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25376
  ] at hbad
  tauto

theorem fin15Anchored_clause27710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom4672 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25376
  ] at hbad
  tauto

theorem fin15Anchored_clause27711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4672 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1795 Fin15AnchoredAtom4672 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25376
  ] at hbad
  tauto

theorem fin15Anchored_clause27712 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4672 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom1664 Fin15AnchoredAtom1674
    Fin15AnchoredAtom1684 Fin15AnchoredAtom1795 Fin15AnchoredAtom4672 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25376
  ] at hbad
  tauto

theorem fin15Anchored_clause27713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom4676 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13600
  ] at hbad
  tauto

theorem fin15Anchored_clause27714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom4676 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13600
  ] at hbad
  tauto

theorem fin15Anchored_clause27715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom4676 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13600
  ] at hbad
  tauto

theorem fin15Anchored_clause27716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom4676 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13600
  ] at hbad
  tauto

theorem fin15Anchored_clause27717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4676 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1799 Fin15AnchoredAtom4676 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13600
  ] at hbad
  tauto

theorem fin15Anchored_clause27718 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4676 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom1667 Fin15AnchoredAtom1672
    Fin15AnchoredAtom1688 Fin15AnchoredAtom1799 Fin15AnchoredAtom4676 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13600
  ] at hbad
  tauto

theorem fin15Anchored_clause27719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom4677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21792
  ] at hbad
  tauto

theorem fin15Anchored_clause27720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1668 Fin15AnchoredAtom4677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21792
  ] at hbad
  tauto

theorem fin15Anchored_clause27721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1673 Fin15AnchoredAtom4677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21792
  ] at hbad
  tauto

theorem fin15Anchored_clause27722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom4677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21792
  ] at hbad
  tauto

theorem fin15Anchored_clause27723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4677 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1800 Fin15AnchoredAtom4677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21792
  ] at hbad
  tauto

theorem fin15Anchored_clause27724 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4677 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1668 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom1668 Fin15AnchoredAtom1673
    Fin15AnchoredAtom1689 Fin15AnchoredAtom1800 Fin15AnchoredAtom4677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21792
  ] at hbad
  tauto

theorem fin15Anchored_clause27725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom4678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25888
  ] at hbad
  tauto

theorem fin15Anchored_clause27726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1668 Fin15AnchoredAtom4678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25888
  ] at hbad
  tauto

theorem fin15Anchored_clause27727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1674 Fin15AnchoredAtom4678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25888
  ] at hbad
  tauto

theorem fin15Anchored_clause27728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom4678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25888
  ] at hbad
  tauto

theorem fin15Anchored_clause27729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4678 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1801 Fin15AnchoredAtom4678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25888
  ] at hbad
  tauto

theorem fin15Anchored_clause27730 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4678 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1668 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom1668 Fin15AnchoredAtom1674
    Fin15AnchoredAtom1690 Fin15AnchoredAtom1801 Fin15AnchoredAtom4678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25888
  ] at hbad
  tauto

theorem fin15Anchored_clause27731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom4682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28960
  ] at hbad
  tauto

theorem fin15Anchored_clause27732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1673 Fin15AnchoredAtom4682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28960
  ] at hbad
  tauto

theorem fin15Anchored_clause27733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1674 Fin15AnchoredAtom4682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28960
  ] at hbad
  tauto

theorem fin15Anchored_clause27734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom4682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28960
  ] at hbad
  tauto

theorem fin15Anchored_clause27735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4682 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1805 Fin15AnchoredAtom4682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28960
  ] at hbad
  tauto

theorem fin15Anchored_clause27736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom1673 Fin15AnchoredAtom1674
    Fin15AnchoredAtom1694 Fin15AnchoredAtom1805 Fin15AnchoredAtom4682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28960
  ] at hbad
  tauto

theorem fin15Anchored_clause27737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4683 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom4683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07712
  ] at hbad
  tauto

theorem fin15Anchored_clause27738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4683 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1679 Fin15AnchoredAtom4683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07712
  ] at hbad
  tauto

theorem fin15Anchored_clause27739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4683 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1806 Fin15AnchoredAtom4683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07712
  ] at hbad
  tauto

theorem fin15Anchored_clause27740 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4683 chi ∧
      Fin15AnchoredAtom1675 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1679 chi ∧
      Fin15AnchoredAtom1685 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom1676 Fin15AnchoredAtom1679
    Fin15AnchoredAtom1685 Fin15AnchoredAtom1806 Fin15AnchoredAtom4683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07712
  ] at hbad
  tauto

theorem fin15Anchored_clause27741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4684 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom4684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11808
  ] at hbad
  tauto

theorem fin15Anchored_clause27742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4684 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom4684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11808
  ] at hbad
  tauto

theorem fin15Anchored_clause27743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4685 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom4685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20000
  ] at hbad
  tauto

theorem fin15Anchored_clause27744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom4686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13856
  ] at hbad
  tauto

theorem fin15Anchored_clause27745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom4686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13856
  ] at hbad
  tauto

theorem fin15Anchored_clause27746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom4686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13856
  ] at hbad
  tauto

theorem fin15Anchored_clause27747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom4686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13856
  ] at hbad
  tauto

theorem fin15Anchored_clause27748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4686 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom4686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13856
  ] at hbad
  tauto

theorem fin15Anchored_clause27749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom1677 Fin15AnchoredAtom1682
    Fin15AnchoredAtom1688 Fin15AnchoredAtom1809 Fin15AnchoredAtom4686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13856
  ] at hbad
  tauto

theorem fin15Anchored_clause27750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom4687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22048
  ] at hbad
  tauto

theorem fin15Anchored_clause27751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom4687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22048
  ] at hbad
  tauto

theorem fin15Anchored_clause27752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom4687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22048
  ] at hbad
  tauto

theorem fin15Anchored_clause27753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom4687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22048
  ] at hbad
  tauto

theorem fin15Anchored_clause27754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4687 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom4687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22048
  ] at hbad
  tauto

theorem fin15Anchored_clause27755 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom1678 Fin15AnchoredAtom1683
    Fin15AnchoredAtom1689 Fin15AnchoredAtom1810 Fin15AnchoredAtom4687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22048
  ] at hbad
  tauto

theorem fin15Anchored_clause27756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom4688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26144
  ] at hbad
  tauto

theorem fin15Anchored_clause27757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom4688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26144
  ] at hbad
  tauto

theorem fin15Anchored_clause27758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom4688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26144
  ] at hbad
  tauto

theorem fin15Anchored_clause27759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom4688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26144
  ] at hbad
  tauto

theorem fin15Anchored_clause27760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4688 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom4688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26144
  ] at hbad
  tauto

theorem fin15Anchored_clause27761 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom1678 Fin15AnchoredAtom1684
    Fin15AnchoredAtom1690 Fin15AnchoredAtom1811 Fin15AnchoredAtom4688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26144
  ] at hbad
  tauto

theorem fin15Anchored_clause27762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4689 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom4689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14880
  ] at hbad
  tauto

theorem fin15Anchored_clause27763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4690 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom4690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23072
  ] at hbad
  tauto

theorem fin15Anchored_clause27764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4690 chi ∧
      ¬Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1813 Fin15AnchoredAtom4690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23072
  ] at hbad
  tauto

theorem fin15Anchored_clause27765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4691 chi ∧
      ¬Fin15AnchoredAtom1681 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1681 Fin15AnchoredAtom4691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27168
  ] at hbad
  tauto

theorem fin15Anchored_clause27766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4691 chi ∧
      ¬Fin15AnchoredAtom1814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1814 Fin15AnchoredAtom4691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27168
  ] at hbad
  tauto

theorem fin15Anchored_clause27767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom4692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29216
  ] at hbad
  tauto

theorem fin15Anchored_clause27768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom4692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29216
  ] at hbad
  tauto

theorem fin15Anchored_clause27769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom4692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29216
  ] at hbad
  tauto

theorem fin15Anchored_clause27770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom4692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29216
  ] at hbad
  tauto

theorem fin15Anchored_clause27771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4692 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom4692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29216
  ] at hbad
  tauto

theorem fin15Anchored_clause27772 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1694 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom1683 Fin15AnchoredAtom1684
    Fin15AnchoredAtom1694 Fin15AnchoredAtom1815 Fin15AnchoredAtom4692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29216
  ] at hbad
  tauto

theorem fin15Anchored_clause27773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1686 Fin15AnchoredAtom4693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15392
  ] at hbad
  tauto

theorem fin15Anchored_clause27774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom4693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15392
  ] at hbad
  tauto

theorem fin15Anchored_clause27775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4693 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1691 Fin15AnchoredAtom4693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15392
  ] at hbad
  tauto

end ErdosSzekeres

end
