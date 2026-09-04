module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 155. -/

theorem fin15Anchored_clause19840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2713 chi ∧
      ¬Fin15AnchoredAtom0781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0781 Fin15AnchoredAtom2713 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18625
  ] at hbad
  tauto

theorem fin15Anchored_clause19841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2713 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom1712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom0742 Fin15AnchoredAtom0760
    Fin15AnchoredAtom0781 Fin15AnchoredAtom1712 Fin15AnchoredAtom2713 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18625
  ] at hbad
  tauto

theorem fin15Anchored_clause19842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12481
  ] at hbad
  tauto

theorem fin15Anchored_clause19843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12481
  ] at hbad
  tauto

theorem fin15Anchored_clause19844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12481
  ] at hbad
  tauto

theorem fin15Anchored_clause19845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12481
  ] at hbad
  tauto

theorem fin15Anchored_clause19846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2714 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom2714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12481
  ] at hbad
  tauto

theorem fin15Anchored_clause19847 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom0741 Fin15AnchoredAtom0761
    Fin15AnchoredAtom0782 Fin15AnchoredAtom1713 Fin15AnchoredAtom2714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12481
  ] at hbad
  tauto

theorem fin15Anchored_clause19848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20673
  ] at hbad
  tauto

theorem fin15Anchored_clause19849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20673
  ] at hbad
  tauto

theorem fin15Anchored_clause19850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20673
  ] at hbad
  tauto

theorem fin15Anchored_clause19851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20673
  ] at hbad
  tauto

theorem fin15Anchored_clause19852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2715 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom2715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20673
  ] at hbad
  tauto

theorem fin15Anchored_clause19853 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom0742 Fin15AnchoredAtom0762
    Fin15AnchoredAtom0783 Fin15AnchoredAtom1714 Fin15AnchoredAtom2715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20673
  ] at hbad
  tauto

theorem fin15Anchored_clause19854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24769
  ] at hbad
  tauto

theorem fin15Anchored_clause19855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24769
  ] at hbad
  tauto

theorem fin15Anchored_clause19856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24769
  ] at hbad
  tauto

theorem fin15Anchored_clause19857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24769
  ] at hbad
  tauto

theorem fin15Anchored_clause19858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2716 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom2716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24769
  ] at hbad
  tauto

theorem fin15Anchored_clause19859 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom0742 Fin15AnchoredAtom0763
    Fin15AnchoredAtom0784 Fin15AnchoredAtom1715 Fin15AnchoredAtom2716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24769
  ] at hbad
  tauto

theorem fin15Anchored_clause19860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom2717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01857
  ] at hbad
  tauto

theorem fin15Anchored_clause19861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom2717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01857
  ] at hbad
  tauto

theorem fin15Anchored_clause19862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01857
  ] at hbad
  tauto

theorem fin15Anchored_clause19863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom2717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01857
  ] at hbad
  tauto

theorem fin15Anchored_clause19864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2717 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom2717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01857
  ] at hbad
  tauto

theorem fin15Anchored_clause19865 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom0744 Fin15AnchoredAtom0749
    Fin15AnchoredAtom0785 Fin15AnchoredAtom1716 Fin15AnchoredAtom2717 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01857
  ] at hbad
  tauto

theorem fin15Anchored_clause19866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom2719 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04929
  ] at hbad
  tauto

theorem fin15Anchored_clause19867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom2719 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04929
  ] at hbad
  tauto

theorem fin15Anchored_clause19868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2719 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04929
  ] at hbad
  tauto

theorem fin15Anchored_clause19869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom2719 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04929
  ] at hbad
  tauto

theorem fin15Anchored_clause19870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2719 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom2719 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04929
  ] at hbad
  tauto

theorem fin15Anchored_clause19871 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom0746 Fin15AnchoredAtom0751
    Fin15AnchoredAtom0787 Fin15AnchoredAtom1718 Fin15AnchoredAtom2719 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04929
  ] at hbad
  tauto

theorem fin15Anchored_clause19872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom2720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09025
  ] at hbad
  tauto

theorem fin15Anchored_clause19873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom2720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09025
  ] at hbad
  tauto

theorem fin15Anchored_clause19874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09025
  ] at hbad
  tauto

theorem fin15Anchored_clause19875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom2720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09025
  ] at hbad
  tauto

theorem fin15Anchored_clause19876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2720 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom2720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09025
  ] at hbad
  tauto

theorem fin15Anchored_clause19877 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom0747 Fin15AnchoredAtom0752
    Fin15AnchoredAtom0788 Fin15AnchoredAtom1719 Fin15AnchoredAtom2720 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09025
  ] at hbad
  tauto

theorem fin15Anchored_clause19878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom2721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17217
  ] at hbad
  tauto

theorem fin15Anchored_clause19879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0748 Fin15AnchoredAtom2721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17217
  ] at hbad
  tauto

theorem fin15Anchored_clause19880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17217
  ] at hbad
  tauto

theorem fin15Anchored_clause19881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0789 Fin15AnchoredAtom2721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17217
  ] at hbad
  tauto

theorem fin15Anchored_clause19882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2721 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1720 Fin15AnchoredAtom2721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17217
  ] at hbad
  tauto

theorem fin15Anchored_clause19883 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom0748 Fin15AnchoredAtom0753
    Fin15AnchoredAtom0789 Fin15AnchoredAtom1720 Fin15AnchoredAtom2721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17217
  ] at hbad
  tauto

theorem fin15Anchored_clause19884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom2723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05441
  ] at hbad
  tauto

theorem fin15Anchored_clause19885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom2723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05441
  ] at hbad
  tauto

theorem fin15Anchored_clause19886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05441
  ] at hbad
  tauto

theorem fin15Anchored_clause19887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom2723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05441
  ] at hbad
  tauto

theorem fin15Anchored_clause19888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2723 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom2723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05441
  ] at hbad
  tauto

theorem fin15Anchored_clause19889 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom0746 Fin15AnchoredAtom0755
    Fin15AnchoredAtom0791 Fin15AnchoredAtom1722 Fin15AnchoredAtom2723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05441
  ] at hbad
  tauto

theorem fin15Anchored_clause19890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom2724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09537
  ] at hbad
  tauto

theorem fin15Anchored_clause19891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom2724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09537
  ] at hbad
  tauto

theorem fin15Anchored_clause19892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09537
  ] at hbad
  tauto

theorem fin15Anchored_clause19893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2724 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09537
  ] at hbad
  tauto

theorem fin15Anchored_clause19894 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom0747 Fin15AnchoredAtom0756
    Fin15AnchoredAtom0792 Fin15AnchoredAtom1723 Fin15AnchoredAtom2724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09537
  ] at hbad
  tauto

theorem fin15Anchored_clause19895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom2725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17729
  ] at hbad
  tauto

theorem fin15Anchored_clause19896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0748 Fin15AnchoredAtom2725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17729
  ] at hbad
  tauto

theorem fin15Anchored_clause19897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17729
  ] at hbad
  tauto

theorem fin15Anchored_clause19898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0793 Fin15AnchoredAtom2725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17729
  ] at hbad
  tauto

theorem fin15Anchored_clause19899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2725 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1724 Fin15AnchoredAtom2725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17729
  ] at hbad
  tauto

theorem fin15Anchored_clause19900 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom0748 Fin15AnchoredAtom0757
    Fin15AnchoredAtom0793 Fin15AnchoredAtom1724 Fin15AnchoredAtom2725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17729
  ] at hbad
  tauto

theorem fin15Anchored_clause19901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom2729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12609
  ] at hbad
  tauto

theorem fin15Anchored_clause19902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom2729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12609
  ] at hbad
  tauto

theorem fin15Anchored_clause19903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12609
  ] at hbad
  tauto

theorem fin15Anchored_clause19904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12609
  ] at hbad
  tauto

theorem fin15Anchored_clause19905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2729 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom2729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12609
  ] at hbad
  tauto

theorem fin15Anchored_clause19906 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom0747 Fin15AnchoredAtom0761
    Fin15AnchoredAtom0797 Fin15AnchoredAtom1728 Fin15AnchoredAtom2729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12609
  ] at hbad
  tauto

theorem fin15Anchored_clause19907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom2730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20801
  ] at hbad
  tauto

theorem fin15Anchored_clause19908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0748 Fin15AnchoredAtom2730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20801
  ] at hbad
  tauto

theorem fin15Anchored_clause19909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20801
  ] at hbad
  tauto

theorem fin15Anchored_clause19910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0798 Fin15AnchoredAtom2730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20801
  ] at hbad
  tauto

theorem fin15Anchored_clause19911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2730 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1729 Fin15AnchoredAtom2730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20801
  ] at hbad
  tauto

theorem fin15Anchored_clause19912 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom0748 Fin15AnchoredAtom0762
    Fin15AnchoredAtom0798 Fin15AnchoredAtom1729 Fin15AnchoredAtom2730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20801
  ] at hbad
  tauto

theorem fin15Anchored_clause19913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom2731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24897
  ] at hbad
  tauto

theorem fin15Anchored_clause19914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0748 Fin15AnchoredAtom2731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24897
  ] at hbad
  tauto

theorem fin15Anchored_clause19915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24897
  ] at hbad
  tauto

theorem fin15Anchored_clause19916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0799 Fin15AnchoredAtom2731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24897
  ] at hbad
  tauto

theorem fin15Anchored_clause19917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2731 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1730 Fin15AnchoredAtom2731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24897
  ] at hbad
  tauto

theorem fin15Anchored_clause19918 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom0748 Fin15AnchoredAtom0763
    Fin15AnchoredAtom0799 Fin15AnchoredAtom1730 Fin15AnchoredAtom2731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24897
  ] at hbad
  tauto

theorem fin15Anchored_clause19919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03649
  ] at hbad
  tauto

theorem fin15Anchored_clause19920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03649
  ] at hbad
  tauto

theorem fin15Anchored_clause19921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom2732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03649
  ] at hbad
  tauto

theorem fin15Anchored_clause19922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03649
  ] at hbad
  tauto

theorem fin15Anchored_clause19923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2732 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1731 Fin15AnchoredAtom2732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03649
  ] at hbad
  tauto

theorem fin15Anchored_clause19924 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2732 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom0750 Fin15AnchoredAtom0754
    Fin15AnchoredAtom0800 Fin15AnchoredAtom1731 Fin15AnchoredAtom2732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03649
  ] at hbad
  tauto

theorem fin15Anchored_clause19925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2733 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05697
  ] at hbad
  tauto

theorem fin15Anchored_clause19926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2733 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05697
  ] at hbad
  tauto

theorem fin15Anchored_clause19927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2733 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05697
  ] at hbad
  tauto

theorem fin15Anchored_clause19928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2733 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05697
  ] at hbad
  tauto

theorem fin15Anchored_clause19929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2733 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom2733 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05697
  ] at hbad
  tauto

theorem fin15Anchored_clause19930 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom0751 Fin15AnchoredAtom0755
    Fin15AnchoredAtom0801 Fin15AnchoredAtom1732 Fin15AnchoredAtom2733 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05697
  ] at hbad
  tauto

theorem fin15Anchored_clause19931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09793
  ] at hbad
  tauto

theorem fin15Anchored_clause19932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09793
  ] at hbad
  tauto

theorem fin15Anchored_clause19933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09793
  ] at hbad
  tauto

theorem fin15Anchored_clause19934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09793
  ] at hbad
  tauto

theorem fin15Anchored_clause19935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2734 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom2734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09793
  ] at hbad
  tauto

theorem fin15Anchored_clause19936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom0752 Fin15AnchoredAtom0756
    Fin15AnchoredAtom0802 Fin15AnchoredAtom1733 Fin15AnchoredAtom2734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09793
  ] at hbad
  tauto

theorem fin15Anchored_clause19937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17985
  ] at hbad
  tauto

theorem fin15Anchored_clause19938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17985
  ] at hbad
  tauto

theorem fin15Anchored_clause19939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17985
  ] at hbad
  tauto

theorem fin15Anchored_clause19940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17985
  ] at hbad
  tauto

theorem fin15Anchored_clause19941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2735 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom2735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17985
  ] at hbad
  tauto

theorem fin15Anchored_clause19942 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom0753 Fin15AnchoredAtom0757
    Fin15AnchoredAtom0803 Fin15AnchoredAtom1734 Fin15AnchoredAtom2735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17985
  ] at hbad
  tauto

theorem fin15Anchored_clause19943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2736 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06721
  ] at hbad
  tauto

theorem fin15Anchored_clause19944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2736 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06721
  ] at hbad
  tauto

theorem fin15Anchored_clause19945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2736 chi ∧
      ¬Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom2736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06721
  ] at hbad
  tauto

theorem fin15Anchored_clause19946 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2736 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom0751 Fin15AnchoredAtom0758
    Fin15AnchoredAtom0804 Fin15AnchoredAtom1735 Fin15AnchoredAtom2736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06721
  ] at hbad
  tauto

theorem fin15Anchored_clause19947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2737 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2737 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10817
  ] at hbad
  tauto

theorem fin15Anchored_clause19948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2737 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2737 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10817
  ] at hbad
  tauto

theorem fin15Anchored_clause19949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2737 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom2737 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10817
  ] at hbad
  tauto

theorem fin15Anchored_clause19950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19009
  ] at hbad
  tauto

theorem fin15Anchored_clause19951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19009
  ] at hbad
  tauto

theorem fin15Anchored_clause19952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom0760 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0760 Fin15AnchoredAtom2738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19009
  ] at hbad
  tauto

theorem fin15Anchored_clause19953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0806 Fin15AnchoredAtom2738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19009
  ] at hbad
  tauto

theorem fin15Anchored_clause19954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2738 chi ∧
      ¬Fin15AnchoredAtom1737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1737 Fin15AnchoredAtom2738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19009
  ] at hbad
  tauto

theorem fin15Anchored_clause19955 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2738 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom1737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom0753 Fin15AnchoredAtom0760
    Fin15AnchoredAtom0806 Fin15AnchoredAtom1737 Fin15AnchoredAtom2738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19009
  ] at hbad
  tauto

theorem fin15Anchored_clause19956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12865
  ] at hbad
  tauto

theorem fin15Anchored_clause19957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12865
  ] at hbad
  tauto

theorem fin15Anchored_clause19958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12865
  ] at hbad
  tauto

theorem fin15Anchored_clause19959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12865
  ] at hbad
  tauto

theorem fin15Anchored_clause19960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2739 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom2739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12865
  ] at hbad
  tauto

theorem fin15Anchored_clause19961 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom0752 Fin15AnchoredAtom0761
    Fin15AnchoredAtom0807 Fin15AnchoredAtom1738 Fin15AnchoredAtom2739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12865
  ] at hbad
  tauto

theorem fin15Anchored_clause19962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21057
  ] at hbad
  tauto

theorem fin15Anchored_clause19963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21057
  ] at hbad
  tauto

theorem fin15Anchored_clause19964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21057
  ] at hbad
  tauto

theorem fin15Anchored_clause19965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21057
  ] at hbad
  tauto

theorem fin15Anchored_clause19966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2740 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom2740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21057
  ] at hbad
  tauto

theorem fin15Anchored_clause19967 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom0753 Fin15AnchoredAtom0762
    Fin15AnchoredAtom0808 Fin15AnchoredAtom1739 Fin15AnchoredAtom2740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21057
  ] at hbad
  tauto

end ErdosSzekeres

end
