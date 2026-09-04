module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 218. -/

theorem fin15Anchored_clause27904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom4724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11456
  ] at hbad
  tauto

theorem fin15Anchored_clause27905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1711 Fin15AnchoredAtom4724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11456
  ] at hbad
  tauto

theorem fin15Anchored_clause27906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1742 Fin15AnchoredAtom4724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11456
  ] at hbad
  tauto

theorem fin15Anchored_clause27907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4724 chi ∧
      ¬Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1777 Fin15AnchoredAtom4724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11456
  ] at hbad
  tauto

theorem fin15Anchored_clause27908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom4725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19648
  ] at hbad
  tauto

theorem fin15Anchored_clause27909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom1743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1743 Fin15AnchoredAtom4725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19648
  ] at hbad
  tauto

theorem fin15Anchored_clause27910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4725 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1778 Fin15AnchoredAtom4725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19648
  ] at hbad
  tauto

theorem fin15Anchored_clause27911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom4726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13504
  ] at hbad
  tauto

theorem fin15Anchored_clause27912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom4726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13504
  ] at hbad
  tauto

theorem fin15Anchored_clause27913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom4726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13504
  ] at hbad
  tauto

theorem fin15Anchored_clause27914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom4726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13504
  ] at hbad
  tauto

theorem fin15Anchored_clause27915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4726 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom4726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13504
  ] at hbad
  tauto

theorem fin15Anchored_clause27916 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4726 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1708 chi ∧
      Fin15AnchoredAtom1713 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom1708 Fin15AnchoredAtom1713
    Fin15AnchoredAtom1744 Fin15AnchoredAtom1779 Fin15AnchoredAtom4726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13504
  ] at hbad
  tauto

theorem fin15Anchored_clause27917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom4727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21696
  ] at hbad
  tauto

theorem fin15Anchored_clause27918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom4727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21696
  ] at hbad
  tauto

theorem fin15Anchored_clause27919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom4727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21696
  ] at hbad
  tauto

theorem fin15Anchored_clause27920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom4727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21696
  ] at hbad
  tauto

theorem fin15Anchored_clause27921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4727 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom4727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21696
  ] at hbad
  tauto

theorem fin15Anchored_clause27922 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4727 chi ∧
      Fin15AnchoredAtom1707 chi ∧
      Fin15AnchoredAtom1709 chi ∧
      Fin15AnchoredAtom1714 chi ∧
      Fin15AnchoredAtom1745 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom1709 Fin15AnchoredAtom1714
    Fin15AnchoredAtom1745 Fin15AnchoredAtom1780 Fin15AnchoredAtom4727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21696
  ] at hbad
  tauto

theorem fin15Anchored_clause27923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom4728 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25792
  ] at hbad
  tauto

theorem fin15Anchored_clause27924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom4728 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25792
  ] at hbad
  tauto

theorem fin15Anchored_clause27925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom4728 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25792
  ] at hbad
  tauto

theorem fin15Anchored_clause27926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom4728 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25792
  ] at hbad
  tauto

theorem fin15Anchored_clause27927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4728 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom4728 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25792
  ] at hbad
  tauto

theorem fin15Anchored_clause27928 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4728 chi ∧
      Fin15AnchoredAtom1708 chi ∧
      Fin15AnchoredAtom1709 chi ∧
      Fin15AnchoredAtom1715 chi ∧
      Fin15AnchoredAtom1746 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom1709 Fin15AnchoredAtom1715
    Fin15AnchoredAtom1746 Fin15AnchoredAtom1781 Fin15AnchoredAtom4728 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25792
  ] at hbad
  tauto

theorem fin15Anchored_clause27929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4729 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom4729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14528
  ] at hbad
  tauto

theorem fin15Anchored_clause27930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4729 chi ∧
      ¬Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1782 Fin15AnchoredAtom4729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14528
  ] at hbad
  tauto

theorem fin15Anchored_clause27931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4730 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom4730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22720
  ] at hbad
  tauto

theorem fin15Anchored_clause27932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4730 chi ∧
      ¬Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1783 Fin15AnchoredAtom4730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22720
  ] at hbad
  tauto

theorem fin15Anchored_clause27933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom4732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28864
  ] at hbad
  tauto

theorem fin15Anchored_clause27934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom4732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28864
  ] at hbad
  tauto

theorem fin15Anchored_clause27935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom4732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28864
  ] at hbad
  tauto

theorem fin15Anchored_clause27936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom4732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28864
  ] at hbad
  tauto

theorem fin15Anchored_clause27937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4732 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom4732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28864
  ] at hbad
  tauto

theorem fin15Anchored_clause27938 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4732 chi ∧
      Fin15AnchoredAtom1713 chi ∧
      Fin15AnchoredAtom1714 chi ∧
      Fin15AnchoredAtom1715 chi ∧
      Fin15AnchoredAtom1750 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom1714 Fin15AnchoredAtom1715
    Fin15AnchoredAtom1750 Fin15AnchoredAtom1785 Fin15AnchoredAtom4732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28864
  ] at hbad
  tauto

theorem fin15Anchored_clause27939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom4734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05952
  ] at hbad
  tauto

theorem fin15Anchored_clause27940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom4734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05952
  ] at hbad
  tauto

theorem fin15Anchored_clause27941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom4734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05952
  ] at hbad
  tauto

theorem fin15Anchored_clause27942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom4734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05952
  ] at hbad
  tauto

theorem fin15Anchored_clause27943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4734 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom4734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05952
  ] at hbad
  tauto

theorem fin15Anchored_clause27944 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4734 chi ∧
      Fin15AnchoredAtom1716 chi ∧
      Fin15AnchoredAtom1718 chi ∧
      Fin15AnchoredAtom1722 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom1718 Fin15AnchoredAtom1722
    Fin15AnchoredAtom1732 Fin15AnchoredAtom1787 Fin15AnchoredAtom4734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05952
  ] at hbad
  tauto

theorem fin15Anchored_clause27945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom4735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10048
  ] at hbad
  tauto

theorem fin15Anchored_clause27946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom4735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10048
  ] at hbad
  tauto

theorem fin15Anchored_clause27947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1723 Fin15AnchoredAtom4735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10048
  ] at hbad
  tauto

theorem fin15Anchored_clause27948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom4735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10048
  ] at hbad
  tauto

theorem fin15Anchored_clause27949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4735 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1788 Fin15AnchoredAtom4735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10048
  ] at hbad
  tauto

theorem fin15Anchored_clause27950 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4735 chi ∧
      Fin15AnchoredAtom1716 chi ∧
      Fin15AnchoredAtom1719 chi ∧
      Fin15AnchoredAtom1723 chi ∧
      Fin15AnchoredAtom1733 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom1719 Fin15AnchoredAtom1723
    Fin15AnchoredAtom1733 Fin15AnchoredAtom1788 Fin15AnchoredAtom4735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10048
  ] at hbad
  tauto

theorem fin15Anchored_clause27951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom4736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18240
  ] at hbad
  tauto

theorem fin15Anchored_clause27952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1720 Fin15AnchoredAtom4736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18240
  ] at hbad
  tauto

theorem fin15Anchored_clause27953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1724 Fin15AnchoredAtom4736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18240
  ] at hbad
  tauto

theorem fin15Anchored_clause27954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom4736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18240
  ] at hbad
  tauto

theorem fin15Anchored_clause27955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4736 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1789 Fin15AnchoredAtom4736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18240
  ] at hbad
  tauto

theorem fin15Anchored_clause27956 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4736 chi ∧
      Fin15AnchoredAtom1716 chi ∧
      Fin15AnchoredAtom1720 chi ∧
      Fin15AnchoredAtom1724 chi ∧
      Fin15AnchoredAtom1734 chi ∧
      Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom1720 Fin15AnchoredAtom1724
    Fin15AnchoredAtom1734 Fin15AnchoredAtom1789 Fin15AnchoredAtom4736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18240
  ] at hbad
  tauto

theorem fin15Anchored_clause27957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom4740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13120
  ] at hbad
  tauto

theorem fin15Anchored_clause27958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom4740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13120
  ] at hbad
  tauto

theorem fin15Anchored_clause27959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom4740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13120
  ] at hbad
  tauto

theorem fin15Anchored_clause27960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom4740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13120
  ] at hbad
  tauto

theorem fin15Anchored_clause27961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4740 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom4740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13120
  ] at hbad
  tauto

theorem fin15Anchored_clause27962 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4740 chi ∧
      Fin15AnchoredAtom1718 chi ∧
      Fin15AnchoredAtom1719 chi ∧
      Fin15AnchoredAtom1728 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom1719 Fin15AnchoredAtom1728
    Fin15AnchoredAtom1738 Fin15AnchoredAtom1793 Fin15AnchoredAtom4740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13120
  ] at hbad
  tauto

theorem fin15Anchored_clause27963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom4741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21312
  ] at hbad
  tauto

theorem fin15Anchored_clause27964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1720 Fin15AnchoredAtom4741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21312
  ] at hbad
  tauto

theorem fin15Anchored_clause27965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1729 Fin15AnchoredAtom4741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21312
  ] at hbad
  tauto

theorem fin15Anchored_clause27966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom4741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21312
  ] at hbad
  tauto

theorem fin15Anchored_clause27967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4741 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1794 Fin15AnchoredAtom4741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21312
  ] at hbad
  tauto

theorem fin15Anchored_clause27968 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4741 chi ∧
      Fin15AnchoredAtom1718 chi ∧
      Fin15AnchoredAtom1720 chi ∧
      Fin15AnchoredAtom1729 chi ∧
      Fin15AnchoredAtom1739 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom1720 Fin15AnchoredAtom1729
    Fin15AnchoredAtom1739 Fin15AnchoredAtom1794 Fin15AnchoredAtom4741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21312
  ] at hbad
  tauto

theorem fin15Anchored_clause27969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom4742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25408
  ] at hbad
  tauto

theorem fin15Anchored_clause27970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1720 Fin15AnchoredAtom4742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25408
  ] at hbad
  tauto

theorem fin15Anchored_clause27971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1730 Fin15AnchoredAtom4742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25408
  ] at hbad
  tauto

theorem fin15Anchored_clause27972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom4742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25408
  ] at hbad
  tauto

theorem fin15Anchored_clause27973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4742 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1795 Fin15AnchoredAtom4742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25408
  ] at hbad
  tauto

theorem fin15Anchored_clause27974 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4742 chi ∧
      Fin15AnchoredAtom1719 chi ∧
      Fin15AnchoredAtom1720 chi ∧
      Fin15AnchoredAtom1730 chi ∧
      Fin15AnchoredAtom1740 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom1720 Fin15AnchoredAtom1730
    Fin15AnchoredAtom1740 Fin15AnchoredAtom1795 Fin15AnchoredAtom4742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25408
  ] at hbad
  tauto

theorem fin15Anchored_clause27975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom4746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13632
  ] at hbad
  tauto

theorem fin15Anchored_clause27976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1723 Fin15AnchoredAtom4746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13632
  ] at hbad
  tauto

theorem fin15Anchored_clause27977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom4746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13632
  ] at hbad
  tauto

theorem fin15Anchored_clause27978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom4746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13632
  ] at hbad
  tauto

theorem fin15Anchored_clause27979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4746 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1799 Fin15AnchoredAtom4746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13632
  ] at hbad
  tauto

theorem fin15Anchored_clause27980 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4746 chi ∧
      Fin15AnchoredAtom1722 chi ∧
      Fin15AnchoredAtom1723 chi ∧
      Fin15AnchoredAtom1728 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom1723 Fin15AnchoredAtom1728
    Fin15AnchoredAtom1744 Fin15AnchoredAtom1799 Fin15AnchoredAtom4746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13632
  ] at hbad
  tauto

theorem fin15Anchored_clause27981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom4747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21824
  ] at hbad
  tauto

theorem fin15Anchored_clause27982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1724 Fin15AnchoredAtom4747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21824
  ] at hbad
  tauto

theorem fin15Anchored_clause27983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom4747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21824
  ] at hbad
  tauto

theorem fin15Anchored_clause27984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4747 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1800 Fin15AnchoredAtom4747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21824
  ] at hbad
  tauto

theorem fin15Anchored_clause27985 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4747 chi ∧
      Fin15AnchoredAtom1722 chi ∧
      Fin15AnchoredAtom1724 chi ∧
      Fin15AnchoredAtom1729 chi ∧
      Fin15AnchoredAtom1745 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom1724 Fin15AnchoredAtom1729
    Fin15AnchoredAtom1745 Fin15AnchoredAtom1800 Fin15AnchoredAtom4747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21824
  ] at hbad
  tauto

theorem fin15Anchored_clause27986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1723 Fin15AnchoredAtom4748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25920
  ] at hbad
  tauto

theorem fin15Anchored_clause27987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1724 Fin15AnchoredAtom4748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25920
  ] at hbad
  tauto

theorem fin15Anchored_clause27988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1730 Fin15AnchoredAtom4748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25920
  ] at hbad
  tauto

theorem fin15Anchored_clause27989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom4748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25920
  ] at hbad
  tauto

theorem fin15Anchored_clause27990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4748 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1801 Fin15AnchoredAtom4748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25920
  ] at hbad
  tauto

theorem fin15Anchored_clause27991 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4748 chi ∧
      Fin15AnchoredAtom1723 chi ∧
      Fin15AnchoredAtom1724 chi ∧
      Fin15AnchoredAtom1730 chi ∧
      Fin15AnchoredAtom1746 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1723 Fin15AnchoredAtom1724 Fin15AnchoredAtom1730
    Fin15AnchoredAtom1746 Fin15AnchoredAtom1801 Fin15AnchoredAtom4748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25920
  ] at hbad
  tauto

theorem fin15Anchored_clause27992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom4752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28992
  ] at hbad
  tauto

theorem fin15Anchored_clause27993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1729 Fin15AnchoredAtom4752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28992
  ] at hbad
  tauto

theorem fin15Anchored_clause27994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1730 Fin15AnchoredAtom4752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28992
  ] at hbad
  tauto

theorem fin15Anchored_clause27995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom4752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28992
  ] at hbad
  tauto

theorem fin15Anchored_clause27996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4752 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1805 Fin15AnchoredAtom4752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28992
  ] at hbad
  tauto

theorem fin15Anchored_clause27997 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4752 chi ∧
      Fin15AnchoredAtom1728 chi ∧
      Fin15AnchoredAtom1729 chi ∧
      Fin15AnchoredAtom1730 chi ∧
      Fin15AnchoredAtom1750 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom1729 Fin15AnchoredAtom1730
    Fin15AnchoredAtom1750 Fin15AnchoredAtom1805 Fin15AnchoredAtom4752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28992
  ] at hbad
  tauto

theorem fin15Anchored_clause27998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom4753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07744
  ] at hbad
  tauto

theorem fin15Anchored_clause27999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom4753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07744
  ] at hbad
  tauto

theorem fin15Anchored_clause28000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4753 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1806 Fin15AnchoredAtom4753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07744
  ] at hbad
  tauto

theorem fin15Anchored_clause28001 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4753 chi ∧
      Fin15AnchoredAtom1731 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1735 chi ∧
      Fin15AnchoredAtom1741 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1731 Fin15AnchoredAtom1732 Fin15AnchoredAtom1735
    Fin15AnchoredAtom1741 Fin15AnchoredAtom1806 Fin15AnchoredAtom4753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07744
  ] at hbad
  tauto

theorem fin15Anchored_clause28002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4754 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom4754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11840
  ] at hbad
  tauto

theorem fin15Anchored_clause28003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4754 chi ∧
      ¬Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1736 Fin15AnchoredAtom4754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11840
  ] at hbad
  tauto

theorem fin15Anchored_clause28004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1731 Fin15AnchoredAtom4755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20032
  ] at hbad
  tauto

theorem fin15Anchored_clause28005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom4755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20032
  ] at hbad
  tauto

theorem fin15Anchored_clause28006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4755 chi ∧
      ¬Fin15AnchoredAtom1808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1808 Fin15AnchoredAtom4755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20032
  ] at hbad
  tauto

theorem fin15Anchored_clause28007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom4756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13888
  ] at hbad
  tauto

theorem fin15Anchored_clause28008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom4756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13888
  ] at hbad
  tauto

theorem fin15Anchored_clause28009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom4756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13888
  ] at hbad
  tauto

theorem fin15Anchored_clause28010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom4756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13888
  ] at hbad
  tauto

theorem fin15Anchored_clause28011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4756 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom4756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13888
  ] at hbad
  tauto

theorem fin15Anchored_clause28012 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4756 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1733 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom1733 Fin15AnchoredAtom1738
    Fin15AnchoredAtom1744 Fin15AnchoredAtom1809 Fin15AnchoredAtom4756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13888
  ] at hbad
  tauto

theorem fin15Anchored_clause28013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom4757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22080
  ] at hbad
  tauto

theorem fin15Anchored_clause28014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom4757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22080
  ] at hbad
  tauto

theorem fin15Anchored_clause28015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom4757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22080
  ] at hbad
  tauto

theorem fin15Anchored_clause28016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom4757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22080
  ] at hbad
  tauto

theorem fin15Anchored_clause28017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4757 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom4757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22080
  ] at hbad
  tauto

theorem fin15Anchored_clause28018 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4757 chi ∧
      Fin15AnchoredAtom1732 chi ∧
      Fin15AnchoredAtom1734 chi ∧
      Fin15AnchoredAtom1739 chi ∧
      Fin15AnchoredAtom1745 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom1734 Fin15AnchoredAtom1739
    Fin15AnchoredAtom1745 Fin15AnchoredAtom1810 Fin15AnchoredAtom4757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22080
  ] at hbad
  tauto

theorem fin15Anchored_clause28019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom4758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26176
  ] at hbad
  tauto

theorem fin15Anchored_clause28020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom4758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26176
  ] at hbad
  tauto

theorem fin15Anchored_clause28021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom4758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26176
  ] at hbad
  tauto

theorem fin15Anchored_clause28022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom4758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26176
  ] at hbad
  tauto

theorem fin15Anchored_clause28023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4758 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom4758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26176
  ] at hbad
  tauto

theorem fin15Anchored_clause28024 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4758 chi ∧
      Fin15AnchoredAtom1733 chi ∧
      Fin15AnchoredAtom1734 chi ∧
      Fin15AnchoredAtom1740 chi ∧
      Fin15AnchoredAtom1746 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom1734 Fin15AnchoredAtom1740
    Fin15AnchoredAtom1746 Fin15AnchoredAtom1811 Fin15AnchoredAtom4758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26176
  ] at hbad
  tauto

theorem fin15Anchored_clause28025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom4759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14912
  ] at hbad
  tauto

theorem fin15Anchored_clause28026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1736 Fin15AnchoredAtom4759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14912
  ] at hbad
  tauto

theorem fin15Anchored_clause28027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4759 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom4759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14912
  ] at hbad
  tauto

theorem fin15Anchored_clause28028 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4759 chi ∧
      Fin15AnchoredAtom1735 chi ∧
      Fin15AnchoredAtom1736 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1747 chi ∧
      Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom1736 Fin15AnchoredAtom1738
    Fin15AnchoredAtom1747 Fin15AnchoredAtom1812 Fin15AnchoredAtom4759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14912
  ] at hbad
  tauto

theorem fin15Anchored_clause28029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4760 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom4760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23104
  ] at hbad
  tauto

theorem fin15Anchored_clause28030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4760 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom4760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23104
  ] at hbad
  tauto

theorem fin15Anchored_clause28031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom4762 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29248
  ] at hbad
  tauto

end ErdosSzekeres

end
