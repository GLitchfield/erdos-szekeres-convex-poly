module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 219. -/

theorem fin15Anchored_clause28032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom4762 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29248
  ] at hbad
  tauto

theorem fin15Anchored_clause28033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom4762 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29248
  ] at hbad
  tauto

theorem fin15Anchored_clause28034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom4762 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29248
  ] at hbad
  tauto

theorem fin15Anchored_clause28035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4762 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom4762 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29248
  ] at hbad
  tauto

theorem fin15Anchored_clause28036 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4762 chi ∧
      Fin15AnchoredAtom1738 chi ∧
      Fin15AnchoredAtom1739 chi ∧
      Fin15AnchoredAtom1740 chi ∧
      Fin15AnchoredAtom1750 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom1739 Fin15AnchoredAtom1740
    Fin15AnchoredAtom1750 Fin15AnchoredAtom1815 Fin15AnchoredAtom4762 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29248
  ] at hbad
  tauto

theorem fin15Anchored_clause28037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1742 Fin15AnchoredAtom4763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15424
  ] at hbad
  tauto

theorem fin15Anchored_clause28038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom4763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15424
  ] at hbad
  tauto

theorem fin15Anchored_clause28039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1747 Fin15AnchoredAtom4763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15424
  ] at hbad
  tauto

theorem fin15Anchored_clause28040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4763 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1816 Fin15AnchoredAtom4763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15424
  ] at hbad
  tauto

theorem fin15Anchored_clause28041 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4763 chi ∧
      Fin15AnchoredAtom1741 chi ∧
      Fin15AnchoredAtom1742 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1747 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1741 Fin15AnchoredAtom1742 Fin15AnchoredAtom1744
    Fin15AnchoredAtom1747 Fin15AnchoredAtom1816 Fin15AnchoredAtom4763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15424
  ] at hbad
  tauto

theorem fin15Anchored_clause28042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4764 chi ∧
      ¬Fin15AnchoredAtom1743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1743 Fin15AnchoredAtom4764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23616
  ] at hbad
  tauto

theorem fin15Anchored_clause28043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4764 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom4764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23616
  ] at hbad
  tauto

theorem fin15Anchored_clause28044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom4766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29760
  ] at hbad
  tauto

theorem fin15Anchored_clause28045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom4766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29760
  ] at hbad
  tauto

theorem fin15Anchored_clause28046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom4766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29760
  ] at hbad
  tauto

theorem fin15Anchored_clause28047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom4766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29760
  ] at hbad
  tauto

theorem fin15Anchored_clause28048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4766 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom4766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29760
  ] at hbad
  tauto

theorem fin15Anchored_clause28049 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4766 chi ∧
      Fin15AnchoredAtom1744 chi ∧
      Fin15AnchoredAtom1745 chi ∧
      Fin15AnchoredAtom1746 chi ∧
      Fin15AnchoredAtom1750 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom1745 Fin15AnchoredAtom1746
    Fin15AnchoredAtom1750 Fin15AnchoredAtom1819 Fin15AnchoredAtom4766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29760
  ] at hbad
  tauto

theorem fin15Anchored_clause28050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom4769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06016
  ] at hbad
  tauto

theorem fin15Anchored_clause28051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom4769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06016
  ] at hbad
  tauto

theorem fin15Anchored_clause28052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom4769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06016
  ] at hbad
  tauto

theorem fin15Anchored_clause28053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom4769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06016
  ] at hbad
  tauto

theorem fin15Anchored_clause28054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4769 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom4769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06016
  ] at hbad
  tauto

theorem fin15Anchored_clause28055 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4769 chi ∧
      Fin15AnchoredAtom1751 chi ∧
      Fin15AnchoredAtom1753 chi ∧
      Fin15AnchoredAtom1757 chi ∧
      Fin15AnchoredAtom1767 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom1753 Fin15AnchoredAtom1757
    Fin15AnchoredAtom1767 Fin15AnchoredAtom1787 Fin15AnchoredAtom4769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06016
  ] at hbad
  tauto

theorem fin15Anchored_clause28056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom4770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10112
  ] at hbad
  tauto

theorem fin15Anchored_clause28057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom4770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10112
  ] at hbad
  tauto

theorem fin15Anchored_clause28058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom4770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10112
  ] at hbad
  tauto

theorem fin15Anchored_clause28059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom4770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10112
  ] at hbad
  tauto

theorem fin15Anchored_clause28060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4770 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1788 Fin15AnchoredAtom4770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10112
  ] at hbad
  tauto

theorem fin15Anchored_clause28061 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4770 chi ∧
      Fin15AnchoredAtom1751 chi ∧
      Fin15AnchoredAtom1754 chi ∧
      Fin15AnchoredAtom1758 chi ∧
      Fin15AnchoredAtom1768 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom1754 Fin15AnchoredAtom1758
    Fin15AnchoredAtom1768 Fin15AnchoredAtom1788 Fin15AnchoredAtom4770 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10112
  ] at hbad
  tauto

theorem fin15Anchored_clause28062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom4771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18304
  ] at hbad
  tauto

theorem fin15Anchored_clause28063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1755 Fin15AnchoredAtom4771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18304
  ] at hbad
  tauto

theorem fin15Anchored_clause28064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1759 Fin15AnchoredAtom4771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18304
  ] at hbad
  tauto

theorem fin15Anchored_clause28065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom4771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18304
  ] at hbad
  tauto

theorem fin15Anchored_clause28066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4771 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1789 Fin15AnchoredAtom4771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18304
  ] at hbad
  tauto

theorem fin15Anchored_clause28067 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4771 chi ∧
      Fin15AnchoredAtom1751 chi ∧
      Fin15AnchoredAtom1755 chi ∧
      Fin15AnchoredAtom1759 chi ∧
      Fin15AnchoredAtom1769 chi ∧
      Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom1755 Fin15AnchoredAtom1759
    Fin15AnchoredAtom1769 Fin15AnchoredAtom1789 Fin15AnchoredAtom4771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18304
  ] at hbad
  tauto

theorem fin15Anchored_clause28068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom4775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13184
  ] at hbad
  tauto

theorem fin15Anchored_clause28069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom4775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13184
  ] at hbad
  tauto

theorem fin15Anchored_clause28070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom4775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13184
  ] at hbad
  tauto

theorem fin15Anchored_clause28071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom4775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13184
  ] at hbad
  tauto

theorem fin15Anchored_clause28072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4775 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom4775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13184
  ] at hbad
  tauto

theorem fin15Anchored_clause28073 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4775 chi ∧
      Fin15AnchoredAtom1753 chi ∧
      Fin15AnchoredAtom1754 chi ∧
      Fin15AnchoredAtom1763 chi ∧
      Fin15AnchoredAtom1773 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom1754 Fin15AnchoredAtom1763
    Fin15AnchoredAtom1773 Fin15AnchoredAtom1793 Fin15AnchoredAtom4775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13184
  ] at hbad
  tauto

theorem fin15Anchored_clause28074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom4776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21376
  ] at hbad
  tauto

theorem fin15Anchored_clause28075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1755 Fin15AnchoredAtom4776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21376
  ] at hbad
  tauto

theorem fin15Anchored_clause28076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1764 Fin15AnchoredAtom4776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21376
  ] at hbad
  tauto

theorem fin15Anchored_clause28077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom4776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21376
  ] at hbad
  tauto

theorem fin15Anchored_clause28078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4776 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1794 Fin15AnchoredAtom4776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21376
  ] at hbad
  tauto

theorem fin15Anchored_clause28079 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4776 chi ∧
      Fin15AnchoredAtom1753 chi ∧
      Fin15AnchoredAtom1755 chi ∧
      Fin15AnchoredAtom1764 chi ∧
      Fin15AnchoredAtom1774 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom1755 Fin15AnchoredAtom1764
    Fin15AnchoredAtom1774 Fin15AnchoredAtom1794 Fin15AnchoredAtom4776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21376
  ] at hbad
  tauto

theorem fin15Anchored_clause28080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom4777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25472
  ] at hbad
  tauto

theorem fin15Anchored_clause28081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1755 Fin15AnchoredAtom4777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25472
  ] at hbad
  tauto

theorem fin15Anchored_clause28082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1765 Fin15AnchoredAtom4777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25472
  ] at hbad
  tauto

theorem fin15Anchored_clause28083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom4777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25472
  ] at hbad
  tauto

theorem fin15Anchored_clause28084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4777 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1795 Fin15AnchoredAtom4777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25472
  ] at hbad
  tauto

theorem fin15Anchored_clause28085 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4777 chi ∧
      Fin15AnchoredAtom1754 chi ∧
      Fin15AnchoredAtom1755 chi ∧
      Fin15AnchoredAtom1765 chi ∧
      Fin15AnchoredAtom1775 chi ∧
      Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom1755 Fin15AnchoredAtom1765
    Fin15AnchoredAtom1775 Fin15AnchoredAtom1795 Fin15AnchoredAtom4777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25472
  ] at hbad
  tauto

theorem fin15Anchored_clause28086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom4781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13696
  ] at hbad
  tauto

theorem fin15Anchored_clause28087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom4781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13696
  ] at hbad
  tauto

theorem fin15Anchored_clause28088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom4781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13696
  ] at hbad
  tauto

theorem fin15Anchored_clause28089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom4781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13696
  ] at hbad
  tauto

theorem fin15Anchored_clause28090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4781 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1799 Fin15AnchoredAtom4781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13696
  ] at hbad
  tauto

theorem fin15Anchored_clause28091 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4781 chi ∧
      Fin15AnchoredAtom1757 chi ∧
      Fin15AnchoredAtom1758 chi ∧
      Fin15AnchoredAtom1763 chi ∧
      Fin15AnchoredAtom1779 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom1758 Fin15AnchoredAtom1763
    Fin15AnchoredAtom1779 Fin15AnchoredAtom1799 Fin15AnchoredAtom4781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13696
  ] at hbad
  tauto

theorem fin15Anchored_clause28092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom4782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21888
  ] at hbad
  tauto

theorem fin15Anchored_clause28093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1759 Fin15AnchoredAtom4782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21888
  ] at hbad
  tauto

theorem fin15Anchored_clause28094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom4782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21888
  ] at hbad
  tauto

theorem fin15Anchored_clause28095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4782 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1800 Fin15AnchoredAtom4782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21888
  ] at hbad
  tauto

theorem fin15Anchored_clause28096 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4782 chi ∧
      Fin15AnchoredAtom1757 chi ∧
      Fin15AnchoredAtom1759 chi ∧
      Fin15AnchoredAtom1764 chi ∧
      Fin15AnchoredAtom1780 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom1759 Fin15AnchoredAtom1764
    Fin15AnchoredAtom1780 Fin15AnchoredAtom1800 Fin15AnchoredAtom4782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21888
  ] at hbad
  tauto

theorem fin15Anchored_clause28097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom4783 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25984
  ] at hbad
  tauto

theorem fin15Anchored_clause28098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1759 Fin15AnchoredAtom4783 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25984
  ] at hbad
  tauto

theorem fin15Anchored_clause28099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom4783 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25984
  ] at hbad
  tauto

theorem fin15Anchored_clause28100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4783 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1801 Fin15AnchoredAtom4783 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25984
  ] at hbad
  tauto

theorem fin15Anchored_clause28101 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4783 chi ∧
      Fin15AnchoredAtom1758 chi ∧
      Fin15AnchoredAtom1759 chi ∧
      Fin15AnchoredAtom1765 chi ∧
      Fin15AnchoredAtom1781 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom1759 Fin15AnchoredAtom1765
    Fin15AnchoredAtom1781 Fin15AnchoredAtom1801 Fin15AnchoredAtom4783 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25984
  ] at hbad
  tauto

theorem fin15Anchored_clause28102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom4787 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29056
  ] at hbad
  tauto

theorem fin15Anchored_clause28103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1764 Fin15AnchoredAtom4787 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29056
  ] at hbad
  tauto

theorem fin15Anchored_clause28104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1765 Fin15AnchoredAtom4787 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29056
  ] at hbad
  tauto

theorem fin15Anchored_clause28105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom4787 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29056
  ] at hbad
  tauto

theorem fin15Anchored_clause28106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4787 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1805 Fin15AnchoredAtom4787 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29056
  ] at hbad
  tauto

theorem fin15Anchored_clause28107 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4787 chi ∧
      Fin15AnchoredAtom1763 chi ∧
      Fin15AnchoredAtom1764 chi ∧
      Fin15AnchoredAtom1765 chi ∧
      Fin15AnchoredAtom1785 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom1764 Fin15AnchoredAtom1765
    Fin15AnchoredAtom1785 Fin15AnchoredAtom1805 Fin15AnchoredAtom4787 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29056
  ] at hbad
  tauto

theorem fin15Anchored_clause28108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom4788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07808
  ] at hbad
  tauto

theorem fin15Anchored_clause28109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom4788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07808
  ] at hbad
  tauto

theorem fin15Anchored_clause28110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1770 Fin15AnchoredAtom4788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07808
  ] at hbad
  tauto

theorem fin15Anchored_clause28111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom4788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07808
  ] at hbad
  tauto

theorem fin15Anchored_clause28112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4788 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1806 Fin15AnchoredAtom4788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07808
  ] at hbad
  tauto

theorem fin15Anchored_clause28113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4788 chi ∧
      Fin15AnchoredAtom1766 chi ∧
      Fin15AnchoredAtom1767 chi ∧
      Fin15AnchoredAtom1770 chi ∧
      Fin15AnchoredAtom1776 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom1767 Fin15AnchoredAtom1770
    Fin15AnchoredAtom1776 Fin15AnchoredAtom1806 Fin15AnchoredAtom4788 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07808
  ] at hbad
  tauto

theorem fin15Anchored_clause28114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4789 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom4789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11904
  ] at hbad
  tauto

theorem fin15Anchored_clause28115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4789 chi ∧
      ¬Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1807 Fin15AnchoredAtom4789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11904
  ] at hbad
  tauto

theorem fin15Anchored_clause28116 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4789 chi ∧
      Fin15AnchoredAtom1766 chi ∧
      Fin15AnchoredAtom1768 chi ∧
      Fin15AnchoredAtom1771 chi ∧
      Fin15AnchoredAtom1777 chi ∧
      Fin15AnchoredAtom1807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom1768 Fin15AnchoredAtom1771
    Fin15AnchoredAtom1777 Fin15AnchoredAtom1807 Fin15AnchoredAtom4789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11904
  ] at hbad
  tauto

theorem fin15Anchored_clause28117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4790 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom4790 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20096
  ] at hbad
  tauto

theorem fin15Anchored_clause28118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4790 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1778 Fin15AnchoredAtom4790 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20096
  ] at hbad
  tauto

theorem fin15Anchored_clause28119 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4790 chi ∧
      Fin15AnchoredAtom1766 chi ∧
      Fin15AnchoredAtom1769 chi ∧
      Fin15AnchoredAtom1772 chi ∧
      Fin15AnchoredAtom1778 chi ∧
      Fin15AnchoredAtom1808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom1769 Fin15AnchoredAtom1772
    Fin15AnchoredAtom1778 Fin15AnchoredAtom1808 Fin15AnchoredAtom4790 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20096
  ] at hbad
  tauto

theorem fin15Anchored_clause28120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom4791 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13952
  ] at hbad
  tauto

theorem fin15Anchored_clause28121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom4791 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13952
  ] at hbad
  tauto

theorem fin15Anchored_clause28122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom4791 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13952
  ] at hbad
  tauto

theorem fin15Anchored_clause28123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom4791 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13952
  ] at hbad
  tauto

theorem fin15Anchored_clause28124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4791 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom4791 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13952
  ] at hbad
  tauto

theorem fin15Anchored_clause28125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4791 chi ∧
      Fin15AnchoredAtom1767 chi ∧
      Fin15AnchoredAtom1768 chi ∧
      Fin15AnchoredAtom1773 chi ∧
      Fin15AnchoredAtom1779 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom1768 Fin15AnchoredAtom1773
    Fin15AnchoredAtom1779 Fin15AnchoredAtom1809 Fin15AnchoredAtom4791 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13952
  ] at hbad
  tauto

theorem fin15Anchored_clause28126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom4792 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22144
  ] at hbad
  tauto

theorem fin15Anchored_clause28127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom4792 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22144
  ] at hbad
  tauto

theorem fin15Anchored_clause28128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom4792 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22144
  ] at hbad
  tauto

theorem fin15Anchored_clause28129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom4792 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22144
  ] at hbad
  tauto

theorem fin15Anchored_clause28130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4792 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom4792 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22144
  ] at hbad
  tauto

theorem fin15Anchored_clause28131 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4792 chi ∧
      Fin15AnchoredAtom1767 chi ∧
      Fin15AnchoredAtom1769 chi ∧
      Fin15AnchoredAtom1774 chi ∧
      Fin15AnchoredAtom1780 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom1769 Fin15AnchoredAtom1774
    Fin15AnchoredAtom1780 Fin15AnchoredAtom1810 Fin15AnchoredAtom4792 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22144
  ] at hbad
  tauto

theorem fin15Anchored_clause28132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom4793 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26240
  ] at hbad
  tauto

theorem fin15Anchored_clause28133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom4793 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26240
  ] at hbad
  tauto

theorem fin15Anchored_clause28134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom4793 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26240
  ] at hbad
  tauto

theorem fin15Anchored_clause28135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom4793 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26240
  ] at hbad
  tauto

theorem fin15Anchored_clause28136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4793 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom4793 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26240
  ] at hbad
  tauto

theorem fin15Anchored_clause28137 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4793 chi ∧
      Fin15AnchoredAtom1768 chi ∧
      Fin15AnchoredAtom1769 chi ∧
      Fin15AnchoredAtom1775 chi ∧
      Fin15AnchoredAtom1781 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom1769 Fin15AnchoredAtom1775
    Fin15AnchoredAtom1781 Fin15AnchoredAtom1811 Fin15AnchoredAtom4793 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26240
  ] at hbad
  tauto

theorem fin15Anchored_clause28138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4794 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1770 Fin15AnchoredAtom4794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14976
  ] at hbad
  tauto

theorem fin15Anchored_clause28139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4794 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom4794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14976
  ] at hbad
  tauto

theorem fin15Anchored_clause28140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4794 chi ∧
      ¬Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1812 Fin15AnchoredAtom4794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14976
  ] at hbad
  tauto

theorem fin15Anchored_clause28141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4795 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom4795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23168
  ] at hbad
  tauto

theorem fin15Anchored_clause28142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4795 chi ∧
      ¬Fin15AnchoredAtom1783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1783 Fin15AnchoredAtom4795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23168
  ] at hbad
  tauto

theorem fin15Anchored_clause28143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4795 chi ∧
      Fin15AnchoredAtom1770 chi ∧
      Fin15AnchoredAtom1772 chi ∧
      Fin15AnchoredAtom1774 chi ∧
      Fin15AnchoredAtom1783 chi ∧
      Fin15AnchoredAtom1813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1770 Fin15AnchoredAtom1772 Fin15AnchoredAtom1774
    Fin15AnchoredAtom1783 Fin15AnchoredAtom1813 Fin15AnchoredAtom4795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23168
  ] at hbad
  tauto

theorem fin15Anchored_clause28144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4796 chi ∧
      ¬Fin15AnchoredAtom1772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1772 Fin15AnchoredAtom4796 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27264
  ] at hbad
  tauto

theorem fin15Anchored_clause28145 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4796 chi ∧
      Fin15AnchoredAtom1771 chi ∧
      Fin15AnchoredAtom1772 chi ∧
      Fin15AnchoredAtom1775 chi ∧
      Fin15AnchoredAtom1784 chi ∧
      Fin15AnchoredAtom1814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1771 Fin15AnchoredAtom1772 Fin15AnchoredAtom1775
    Fin15AnchoredAtom1784 Fin15AnchoredAtom1814 Fin15AnchoredAtom4796 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27264
  ] at hbad
  tauto

theorem fin15Anchored_clause28146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom4797 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29312
  ] at hbad
  tauto

theorem fin15Anchored_clause28147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom4797 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29312
  ] at hbad
  tauto

theorem fin15Anchored_clause28148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom4797 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29312
  ] at hbad
  tauto

theorem fin15Anchored_clause28149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom4797 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29312
  ] at hbad
  tauto

theorem fin15Anchored_clause28150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4797 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom4797 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29312
  ] at hbad
  tauto

theorem fin15Anchored_clause28151 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4797 chi ∧
      Fin15AnchoredAtom1773 chi ∧
      Fin15AnchoredAtom1774 chi ∧
      Fin15AnchoredAtom1775 chi ∧
      Fin15AnchoredAtom1785 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom1774 Fin15AnchoredAtom1775
    Fin15AnchoredAtom1785 Fin15AnchoredAtom1815 Fin15AnchoredAtom4797 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29312
  ] at hbad
  tauto

theorem fin15Anchored_clause28152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom4798 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15488
  ] at hbad
  tauto

theorem fin15Anchored_clause28153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom4798 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15488
  ] at hbad
  tauto

theorem fin15Anchored_clause28154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1782 Fin15AnchoredAtom4798 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15488
  ] at hbad
  tauto

theorem fin15Anchored_clause28155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4798 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1816 Fin15AnchoredAtom4798 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15488
  ] at hbad
  tauto

theorem fin15Anchored_clause28156 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4798 chi ∧
      Fin15AnchoredAtom1776 chi ∧
      Fin15AnchoredAtom1777 chi ∧
      Fin15AnchoredAtom1779 chi ∧
      Fin15AnchoredAtom1782 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom1777 Fin15AnchoredAtom1779
    Fin15AnchoredAtom1782 Fin15AnchoredAtom1816 Fin15AnchoredAtom4798 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15488
  ] at hbad
  tauto

theorem fin15Anchored_clause28157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4799 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1778 Fin15AnchoredAtom4799 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23680
  ] at hbad
  tauto

theorem fin15Anchored_clause28158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4799 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom4799 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23680
  ] at hbad
  tauto

theorem fin15Anchored_clause28159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4799 chi ∧
      ¬Fin15AnchoredAtom1817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1817 Fin15AnchoredAtom4799 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23680
  ] at hbad
  tauto

end ErdosSzekeres

end
