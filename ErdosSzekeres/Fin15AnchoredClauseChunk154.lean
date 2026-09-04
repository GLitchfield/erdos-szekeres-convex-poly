module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 154. -/

theorem fin15Anchored_clause19712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom2689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13345
  ] at hbad
  tauto

theorem fin15Anchored_clause19713 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom0728 Fin15AnchoredAtom0733
    Fin15AnchoredAtom0813 Fin15AnchoredAtom1688 Fin15AnchoredAtom2689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13345
  ] at hbad
  tauto

theorem fin15Anchored_clause19714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21537
  ] at hbad
  tauto

theorem fin15Anchored_clause19715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21537
  ] at hbad
  tauto

theorem fin15Anchored_clause19716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21537
  ] at hbad
  tauto

theorem fin15Anchored_clause19717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21537
  ] at hbad
  tauto

theorem fin15Anchored_clause19718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2690 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom2690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21537
  ] at hbad
  tauto

theorem fin15Anchored_clause19719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom0729 Fin15AnchoredAtom0734
    Fin15AnchoredAtom0814 Fin15AnchoredAtom1689 Fin15AnchoredAtom2690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21537
  ] at hbad
  tauto

theorem fin15Anchored_clause19720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25633
  ] at hbad
  tauto

theorem fin15Anchored_clause19721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25633
  ] at hbad
  tauto

theorem fin15Anchored_clause19722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25633
  ] at hbad
  tauto

theorem fin15Anchored_clause19723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25633
  ] at hbad
  tauto

theorem fin15Anchored_clause19724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2691 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom2691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25633
  ] at hbad
  tauto

theorem fin15Anchored_clause19725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom0729 Fin15AnchoredAtom0735
    Fin15AnchoredAtom0815 Fin15AnchoredAtom1690 Fin15AnchoredAtom2691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25633
  ] at hbad
  tauto

theorem fin15Anchored_clause19726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom2692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14369
  ] at hbad
  tauto

theorem fin15Anchored_clause19727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom0731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0731 Fin15AnchoredAtom2692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14369
  ] at hbad
  tauto

theorem fin15Anchored_clause19728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14369
  ] at hbad
  tauto

theorem fin15Anchored_clause19729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0816 Fin15AnchoredAtom2692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14369
  ] at hbad
  tauto

theorem fin15Anchored_clause19730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2692 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1691 Fin15AnchoredAtom2692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14369
  ] at hbad
  tauto

theorem fin15Anchored_clause19731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2692 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom0731 Fin15AnchoredAtom0733
    Fin15AnchoredAtom0816 Fin15AnchoredAtom1691 Fin15AnchoredAtom2692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14369
  ] at hbad
  tauto

theorem fin15Anchored_clause19732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom2693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22561
  ] at hbad
  tauto

theorem fin15Anchored_clause19733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom0732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0732 Fin15AnchoredAtom2693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22561
  ] at hbad
  tauto

theorem fin15Anchored_clause19734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22561
  ] at hbad
  tauto

theorem fin15Anchored_clause19735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2693 chi ∧
      ¬Fin15AnchoredAtom0817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0817 Fin15AnchoredAtom2693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22561
  ] at hbad
  tauto

theorem fin15Anchored_clause19736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2693 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom0732 Fin15AnchoredAtom0734
    Fin15AnchoredAtom0817 Fin15AnchoredAtom1692 Fin15AnchoredAtom2693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22561
  ] at hbad
  tauto

theorem fin15Anchored_clause19737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2694 chi ∧
      ¬Fin15AnchoredAtom0731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0731 Fin15AnchoredAtom2694 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26657
  ] at hbad
  tauto

theorem fin15Anchored_clause19738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2694 chi ∧
      ¬Fin15AnchoredAtom0732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0732 Fin15AnchoredAtom2694 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26657
  ] at hbad
  tauto

theorem fin15Anchored_clause19739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2694 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2694 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26657
  ] at hbad
  tauto

theorem fin15Anchored_clause19740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2694 chi ∧
      ¬Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1693 Fin15AnchoredAtom2694 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26657
  ] at hbad
  tauto

theorem fin15Anchored_clause19741 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2694 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0818 chi ∧
      Fin15AnchoredAtom1693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0731 Fin15AnchoredAtom0732 Fin15AnchoredAtom0735
    Fin15AnchoredAtom0818 Fin15AnchoredAtom1693 Fin15AnchoredAtom2694 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26657
  ] at hbad
  tauto

theorem fin15Anchored_clause19742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28705
  ] at hbad
  tauto

theorem fin15Anchored_clause19743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28705
  ] at hbad
  tauto

theorem fin15Anchored_clause19744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28705
  ] at hbad
  tauto

theorem fin15Anchored_clause19745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28705
  ] at hbad
  tauto

theorem fin15Anchored_clause19746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2695 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom2695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28705
  ] at hbad
  tauto

theorem fin15Anchored_clause19747 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom0734 Fin15AnchoredAtom0735
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1694 Fin15AnchoredAtom2695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28705
  ] at hbad
  tauto

theorem fin15Anchored_clause19748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom2696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00961
  ] at hbad
  tauto

theorem fin15Anchored_clause19749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00961
  ] at hbad
  tauto

theorem fin15Anchored_clause19750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom2696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00961
  ] at hbad
  tauto

theorem fin15Anchored_clause19751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom2696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00961
  ] at hbad
  tauto

theorem fin15Anchored_clause19752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2696 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom2696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00961
  ] at hbad
  tauto

theorem fin15Anchored_clause19753 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom0737 Fin15AnchoredAtom0743
    Fin15AnchoredAtom0764 Fin15AnchoredAtom1695 Fin15AnchoredAtom2696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00961
  ] at hbad
  tauto

theorem fin15Anchored_clause19754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom2697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01473
  ] at hbad
  tauto

theorem fin15Anchored_clause19755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01473
  ] at hbad
  tauto

theorem fin15Anchored_clause19756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom2697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01473
  ] at hbad
  tauto

theorem fin15Anchored_clause19757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom2697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01473
  ] at hbad
  tauto

theorem fin15Anchored_clause19758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2697 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom2697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01473
  ] at hbad
  tauto

theorem fin15Anchored_clause19759 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom0738 Fin15AnchoredAtom0744
    Fin15AnchoredAtom0765 Fin15AnchoredAtom1696 Fin15AnchoredAtom2697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01473
  ] at hbad
  tauto

theorem fin15Anchored_clause19760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom2699 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04545
  ] at hbad
  tauto

theorem fin15Anchored_clause19761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2699 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04545
  ] at hbad
  tauto

theorem fin15Anchored_clause19762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom2699 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04545
  ] at hbad
  tauto

theorem fin15Anchored_clause19763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2699 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom2699 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04545
  ] at hbad
  tauto

theorem fin15Anchored_clause19764 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2699 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom0740 Fin15AnchoredAtom0746
    Fin15AnchoredAtom0767 Fin15AnchoredAtom1698 Fin15AnchoredAtom2699 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04545
  ] at hbad
  tauto

theorem fin15Anchored_clause19765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom2700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08641
  ] at hbad
  tauto

theorem fin15Anchored_clause19766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08641
  ] at hbad
  tauto

theorem fin15Anchored_clause19767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom2700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08641
  ] at hbad
  tauto

theorem fin15Anchored_clause19768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0768 Fin15AnchoredAtom2700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08641
  ] at hbad
  tauto

theorem fin15Anchored_clause19769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2700 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom2700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08641
  ] at hbad
  tauto

theorem fin15Anchored_clause19770 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom0741 Fin15AnchoredAtom0747
    Fin15AnchoredAtom0768 Fin15AnchoredAtom1699 Fin15AnchoredAtom2700 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08641
  ] at hbad
  tauto

theorem fin15Anchored_clause19771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom2701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16833
  ] at hbad
  tauto

theorem fin15Anchored_clause19772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16833
  ] at hbad
  tauto

theorem fin15Anchored_clause19773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0748 Fin15AnchoredAtom2701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16833
  ] at hbad
  tauto

theorem fin15Anchored_clause19774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0769 Fin15AnchoredAtom2701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16833
  ] at hbad
  tauto

theorem fin15Anchored_clause19775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2701 chi ∧
      ¬Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1700 Fin15AnchoredAtom2701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16833
  ] at hbad
  tauto

theorem fin15Anchored_clause19776 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom0742 Fin15AnchoredAtom0748
    Fin15AnchoredAtom0769 Fin15AnchoredAtom1700 Fin15AnchoredAtom2701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16833
  ] at hbad
  tauto

theorem fin15Anchored_clause19777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01729
  ] at hbad
  tauto

theorem fin15Anchored_clause19778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01729
  ] at hbad
  tauto

theorem fin15Anchored_clause19779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01729
  ] at hbad
  tauto

theorem fin15Anchored_clause19780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01729
  ] at hbad
  tauto

theorem fin15Anchored_clause19781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2702 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom2702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01729
  ] at hbad
  tauto

theorem fin15Anchored_clause19782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom0738 Fin15AnchoredAtom0749
    Fin15AnchoredAtom0770 Fin15AnchoredAtom1701 Fin15AnchoredAtom2702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01729
  ] at hbad
  tauto

theorem fin15Anchored_clause19783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2703 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02753
  ] at hbad
  tauto

theorem fin15Anchored_clause19784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom2703 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02753
  ] at hbad
  tauto

theorem fin15Anchored_clause19785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2703 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02753
  ] at hbad
  tauto

theorem fin15Anchored_clause19786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom2703 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02753
  ] at hbad
  tauto

theorem fin15Anchored_clause19787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2703 chi ∧
      ¬Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1702 Fin15AnchoredAtom2703 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02753
  ] at hbad
  tauto

theorem fin15Anchored_clause19788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2703 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom0739 Fin15AnchoredAtom0750
    Fin15AnchoredAtom0771 Fin15AnchoredAtom1702 Fin15AnchoredAtom2703 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02753
  ] at hbad
  tauto

theorem fin15Anchored_clause19789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04801
  ] at hbad
  tauto

theorem fin15Anchored_clause19790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04801
  ] at hbad
  tauto

theorem fin15Anchored_clause19791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04801
  ] at hbad
  tauto

theorem fin15Anchored_clause19792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04801
  ] at hbad
  tauto

theorem fin15Anchored_clause19793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2704 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom2704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04801
  ] at hbad
  tauto

theorem fin15Anchored_clause19794 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom0740 Fin15AnchoredAtom0751
    Fin15AnchoredAtom0772 Fin15AnchoredAtom1703 Fin15AnchoredAtom2704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04801
  ] at hbad
  tauto

theorem fin15Anchored_clause19795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08897
  ] at hbad
  tauto

theorem fin15Anchored_clause19796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08897
  ] at hbad
  tauto

theorem fin15Anchored_clause19797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08897
  ] at hbad
  tauto

theorem fin15Anchored_clause19798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08897
  ] at hbad
  tauto

theorem fin15Anchored_clause19799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2705 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom2705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08897
  ] at hbad
  tauto

theorem fin15Anchored_clause19800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom0741 Fin15AnchoredAtom0752
    Fin15AnchoredAtom0773 Fin15AnchoredAtom1704 Fin15AnchoredAtom2705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08897
  ] at hbad
  tauto

theorem fin15Anchored_clause19801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17089
  ] at hbad
  tauto

theorem fin15Anchored_clause19802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17089
  ] at hbad
  tauto

theorem fin15Anchored_clause19803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17089
  ] at hbad
  tauto

theorem fin15Anchored_clause19804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17089
  ] at hbad
  tauto

theorem fin15Anchored_clause19805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2706 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom2706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17089
  ] at hbad
  tauto

theorem fin15Anchored_clause19806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom0742 Fin15AnchoredAtom0753
    Fin15AnchoredAtom0774 Fin15AnchoredAtom1705 Fin15AnchoredAtom2706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17089
  ] at hbad
  tauto

theorem fin15Anchored_clause19807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03265
  ] at hbad
  tauto

theorem fin15Anchored_clause19808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom2707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03265
  ] at hbad
  tauto

theorem fin15Anchored_clause19809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2707 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03265
  ] at hbad
  tauto

theorem fin15Anchored_clause19810 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2707 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom0739 Fin15AnchoredAtom0754
    Fin15AnchoredAtom0775 Fin15AnchoredAtom1706 Fin15AnchoredAtom2707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03265
  ] at hbad
  tauto

theorem fin15Anchored_clause19811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05313
  ] at hbad
  tauto

theorem fin15Anchored_clause19812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05313
  ] at hbad
  tauto

theorem fin15Anchored_clause19813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05313
  ] at hbad
  tauto

theorem fin15Anchored_clause19814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05313
  ] at hbad
  tauto

theorem fin15Anchored_clause19815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2708 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom2708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05313
  ] at hbad
  tauto

theorem fin15Anchored_clause19816 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom0740 Fin15AnchoredAtom0755
    Fin15AnchoredAtom0776 Fin15AnchoredAtom1707 Fin15AnchoredAtom2708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05313
  ] at hbad
  tauto

theorem fin15Anchored_clause19817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09409
  ] at hbad
  tauto

theorem fin15Anchored_clause19818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09409
  ] at hbad
  tauto

theorem fin15Anchored_clause19819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09409
  ] at hbad
  tauto

theorem fin15Anchored_clause19820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09409
  ] at hbad
  tauto

theorem fin15Anchored_clause19821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2709 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom2709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09409
  ] at hbad
  tauto

theorem fin15Anchored_clause19822 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom0741 Fin15AnchoredAtom0756
    Fin15AnchoredAtom0777 Fin15AnchoredAtom1708 Fin15AnchoredAtom2709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09409
  ] at hbad
  tauto

theorem fin15Anchored_clause19823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17601
  ] at hbad
  tauto

theorem fin15Anchored_clause19824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17601
  ] at hbad
  tauto

theorem fin15Anchored_clause19825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17601
  ] at hbad
  tauto

theorem fin15Anchored_clause19826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17601
  ] at hbad
  tauto

theorem fin15Anchored_clause19827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2710 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom2710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17601
  ] at hbad
  tauto

theorem fin15Anchored_clause19828 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom0742 Fin15AnchoredAtom0757
    Fin15AnchoredAtom0778 Fin15AnchoredAtom1709 Fin15AnchoredAtom2710 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17601
  ] at hbad
  tauto

theorem fin15Anchored_clause19829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom2711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06337
  ] at hbad
  tauto

theorem fin15Anchored_clause19830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06337
  ] at hbad
  tauto

theorem fin15Anchored_clause19831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2711 chi ∧
      ¬Fin15AnchoredAtom0779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0779 Fin15AnchoredAtom2711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06337
  ] at hbad
  tauto

theorem fin15Anchored_clause19832 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2711 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom0740 Fin15AnchoredAtom0758
    Fin15AnchoredAtom0779 Fin15AnchoredAtom1710 Fin15AnchoredAtom2711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06337
  ] at hbad
  tauto

theorem fin15Anchored_clause19833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom2712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10433
  ] at hbad
  tauto

theorem fin15Anchored_clause19834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10433
  ] at hbad
  tauto

theorem fin15Anchored_clause19835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom0759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0759 Fin15AnchoredAtom2712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10433
  ] at hbad
  tauto

theorem fin15Anchored_clause19836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0780 Fin15AnchoredAtom2712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10433
  ] at hbad
  tauto

theorem fin15Anchored_clause19837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2712 chi ∧
      ¬Fin15AnchoredAtom1711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1711 Fin15AnchoredAtom2712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10433
  ] at hbad
  tauto

theorem fin15Anchored_clause19838 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2712 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom1711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom0741 Fin15AnchoredAtom0759
    Fin15AnchoredAtom0780 Fin15AnchoredAtom1711 Fin15AnchoredAtom2712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10433
  ] at hbad
  tauto

theorem fin15Anchored_clause19839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2713 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2713 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18625
  ] at hbad
  tauto

end ErdosSzekeres

end
