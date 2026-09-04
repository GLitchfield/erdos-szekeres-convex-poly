module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 162. -/

theorem fin15Anchored_clause20736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2917 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0881 chi ∧
      Fin15AnchoredAtom0981 chi ∧
      Fin15AnchoredAtom1201 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0837 Fin15AnchoredAtom0839 Fin15AnchoredAtom0881
    Fin15AnchoredAtom0981 Fin15AnchoredAtom1201 Fin15AnchoredAtom2917 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10262
  ] at hbad
  tauto

theorem fin15Anchored_clause20737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom2919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12310
  ] at hbad
  tauto

theorem fin15Anchored_clause20738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom2919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12310
  ] at hbad
  tauto

theorem fin15Anchored_clause20739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom2919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12310
  ] at hbad
  tauto

theorem fin15Anchored_clause20740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom2919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12310
  ] at hbad
  tauto

theorem fin15Anchored_clause20741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom2919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12310
  ] at hbad
  tauto

theorem fin15Anchored_clause20742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2919 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom0839 Fin15AnchoredAtom0883
    Fin15AnchoredAtom0983 Fin15AnchoredAtom1203 Fin15AnchoredAtom2919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12310
  ] at hbad
  tauto

theorem fin15Anchored_clause20743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom2920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20502
  ] at hbad
  tauto

theorem fin15Anchored_clause20744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom2920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20502
  ] at hbad
  tauto

theorem fin15Anchored_clause20745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0884 Fin15AnchoredAtom2920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20502
  ] at hbad
  tauto

theorem fin15Anchored_clause20746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom2920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20502
  ] at hbad
  tauto

theorem fin15Anchored_clause20747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom2920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20502
  ] at hbad
  tauto

theorem fin15Anchored_clause20748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2920 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom0840 Fin15AnchoredAtom0884
    Fin15AnchoredAtom0984 Fin15AnchoredAtom1204 Fin15AnchoredAtom2920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20502
  ] at hbad
  tauto

theorem fin15Anchored_clause20749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom2921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24598
  ] at hbad
  tauto

theorem fin15Anchored_clause20750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom2921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24598
  ] at hbad
  tauto

theorem fin15Anchored_clause20751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0885 Fin15AnchoredAtom2921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24598
  ] at hbad
  tauto

theorem fin15Anchored_clause20752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom2921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24598
  ] at hbad
  tauto

theorem fin15Anchored_clause20753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1205 Fin15AnchoredAtom2921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24598
  ] at hbad
  tauto

theorem fin15Anchored_clause20754 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2921 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom0840 Fin15AnchoredAtom0885
    Fin15AnchoredAtom0985 Fin15AnchoredAtom1205 Fin15AnchoredAtom2921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24598
  ] at hbad
  tauto

theorem fin15Anchored_clause20755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom2922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00230
  ] at hbad
  tauto

theorem fin15Anchored_clause20756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom2922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00230
  ] at hbad
  tauto

theorem fin15Anchored_clause20757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00230
  ] at hbad
  tauto

theorem fin15Anchored_clause20758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom2922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00230
  ] at hbad
  tauto

theorem fin15Anchored_clause20759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom2922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00230
  ] at hbad
  tauto

theorem fin15Anchored_clause20760 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2922 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom0842 Fin15AnchoredAtom0850
    Fin15AnchoredAtom0986 Fin15AnchoredAtom1206 Fin15AnchoredAtom2922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00230
  ] at hbad
  tauto

theorem fin15Anchored_clause20761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2923 chi ∧
      ¬Fin15AnchoredAtom0843 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0843 Fin15AnchoredAtom2923 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00358
  ] at hbad
  tauto

theorem fin15Anchored_clause20762 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2923 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0851 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom1207 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom0843 Fin15AnchoredAtom0851
    Fin15AnchoredAtom0987 Fin15AnchoredAtom1207 Fin15AnchoredAtom2923 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00358
  ] at hbad
  tauto

theorem fin15Anchored_clause20763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom2924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00614
  ] at hbad
  tauto

theorem fin15Anchored_clause20764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom2924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00614
  ] at hbad
  tauto

theorem fin15Anchored_clause20765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom2924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00614
  ] at hbad
  tauto

theorem fin15Anchored_clause20766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom2924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00614
  ] at hbad
  tauto

theorem fin15Anchored_clause20767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom2924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00614
  ] at hbad
  tauto

theorem fin15Anchored_clause20768 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2924 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom0844 Fin15AnchoredAtom0852
    Fin15AnchoredAtom0988 Fin15AnchoredAtom1208 Fin15AnchoredAtom2924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00614
  ] at hbad
  tauto

theorem fin15Anchored_clause20769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom2925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01126
  ] at hbad
  tauto

theorem fin15Anchored_clause20770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom2925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01126
  ] at hbad
  tauto

theorem fin15Anchored_clause20771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01126
  ] at hbad
  tauto

theorem fin15Anchored_clause20772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom2925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01126
  ] at hbad
  tauto

theorem fin15Anchored_clause20773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom2925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01126
  ] at hbad
  tauto

theorem fin15Anchored_clause20774 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2925 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom0845 Fin15AnchoredAtom0853
    Fin15AnchoredAtom0989 Fin15AnchoredAtom1209 Fin15AnchoredAtom2925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01126
  ] at hbad
  tauto

theorem fin15Anchored_clause20775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2926 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom2926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02150
  ] at hbad
  tauto

theorem fin15Anchored_clause20776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2926 chi ∧
      ¬Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1210 Fin15AnchoredAtom2926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02150
  ] at hbad
  tauto

theorem fin15Anchored_clause20777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2926 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0846 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0990 chi ∧
      Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom0846 Fin15AnchoredAtom0854
    Fin15AnchoredAtom0990 Fin15AnchoredAtom1210 Fin15AnchoredAtom2926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02150
  ] at hbad
  tauto

theorem fin15Anchored_clause20778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom2927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04198
  ] at hbad
  tauto

theorem fin15Anchored_clause20779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom2927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04198
  ] at hbad
  tauto

theorem fin15Anchored_clause20780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom2927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04198
  ] at hbad
  tauto

theorem fin15Anchored_clause20781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom2927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04198
  ] at hbad
  tauto

theorem fin15Anchored_clause20782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom2927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04198
  ] at hbad
  tauto

theorem fin15Anchored_clause20783 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2927 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom0847 Fin15AnchoredAtom0855
    Fin15AnchoredAtom0991 Fin15AnchoredAtom1211 Fin15AnchoredAtom2927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04198
  ] at hbad
  tauto

theorem fin15Anchored_clause20784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom2928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08294
  ] at hbad
  tauto

theorem fin15Anchored_clause20785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom2928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08294
  ] at hbad
  tauto

theorem fin15Anchored_clause20786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom2928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08294
  ] at hbad
  tauto

theorem fin15Anchored_clause20787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom2928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08294
  ] at hbad
  tauto

theorem fin15Anchored_clause20788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom2928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08294
  ] at hbad
  tauto

theorem fin15Anchored_clause20789 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2928 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom0848 Fin15AnchoredAtom0856
    Fin15AnchoredAtom0992 Fin15AnchoredAtom1212 Fin15AnchoredAtom2928 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08294
  ] at hbad
  tauto

theorem fin15Anchored_clause20790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom2929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16486
  ] at hbad
  tauto

theorem fin15Anchored_clause20791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0849 Fin15AnchoredAtom2929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16486
  ] at hbad
  tauto

theorem fin15Anchored_clause20792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom2929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16486
  ] at hbad
  tauto

theorem fin15Anchored_clause20793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom2929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16486
  ] at hbad
  tauto

theorem fin15Anchored_clause20794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom2929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16486
  ] at hbad
  tauto

theorem fin15Anchored_clause20795 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2929 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom0849 Fin15AnchoredAtom0857
    Fin15AnchoredAtom0993 Fin15AnchoredAtom1213 Fin15AnchoredAtom2929 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16486
  ] at hbad
  tauto

theorem fin15Anchored_clause20796 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2930 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0858 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom0843 Fin15AnchoredAtom0858
    Fin15AnchoredAtom0994 Fin15AnchoredAtom1214 Fin15AnchoredAtom2930 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00422
  ] at hbad
  tauto

theorem fin15Anchored_clause20797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom2931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00678
  ] at hbad
  tauto

theorem fin15Anchored_clause20798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom2931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00678
  ] at hbad
  tauto

theorem fin15Anchored_clause20799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom2931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00678
  ] at hbad
  tauto

theorem fin15Anchored_clause20800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom2931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00678
  ] at hbad
  tauto

theorem fin15Anchored_clause20801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom2931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00678
  ] at hbad
  tauto

theorem fin15Anchored_clause20802 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2931 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom0844 Fin15AnchoredAtom0859
    Fin15AnchoredAtom0995 Fin15AnchoredAtom1215 Fin15AnchoredAtom2931 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00678
  ] at hbad
  tauto

theorem fin15Anchored_clause20803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom2932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01190
  ] at hbad
  tauto

theorem fin15Anchored_clause20804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom2932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01190
  ] at hbad
  tauto

theorem fin15Anchored_clause20805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom2932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01190
  ] at hbad
  tauto

theorem fin15Anchored_clause20806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom2932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01190
  ] at hbad
  tauto

theorem fin15Anchored_clause20807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom2932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01190
  ] at hbad
  tauto

theorem fin15Anchored_clause20808 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2932 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom0845 Fin15AnchoredAtom0860
    Fin15AnchoredAtom0996 Fin15AnchoredAtom1216 Fin15AnchoredAtom2932 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01190
  ] at hbad
  tauto

theorem fin15Anchored_clause20809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2933 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom2933 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02214
  ] at hbad
  tauto

theorem fin15Anchored_clause20810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2933 chi ∧
      ¬Fin15AnchoredAtom1217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1217 Fin15AnchoredAtom2933 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02214
  ] at hbad
  tauto

theorem fin15Anchored_clause20811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom2934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04262
  ] at hbad
  tauto

theorem fin15Anchored_clause20812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom2934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04262
  ] at hbad
  tauto

theorem fin15Anchored_clause20813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom2934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04262
  ] at hbad
  tauto

theorem fin15Anchored_clause20814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom2934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04262
  ] at hbad
  tauto

theorem fin15Anchored_clause20815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom2934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04262
  ] at hbad
  tauto

theorem fin15Anchored_clause20816 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2934 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom0847 Fin15AnchoredAtom0862
    Fin15AnchoredAtom0998 Fin15AnchoredAtom1218 Fin15AnchoredAtom2934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04262
  ] at hbad
  tauto

theorem fin15Anchored_clause20817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom2935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08358
  ] at hbad
  tauto

theorem fin15Anchored_clause20818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom2935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08358
  ] at hbad
  tauto

theorem fin15Anchored_clause20819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom2935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08358
  ] at hbad
  tauto

theorem fin15Anchored_clause20820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom2935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08358
  ] at hbad
  tauto

theorem fin15Anchored_clause20821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom2935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08358
  ] at hbad
  tauto

theorem fin15Anchored_clause20822 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2935 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom0848 Fin15AnchoredAtom0863
    Fin15AnchoredAtom0999 Fin15AnchoredAtom1219 Fin15AnchoredAtom2935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08358
  ] at hbad
  tauto

theorem fin15Anchored_clause20823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom2936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16550
  ] at hbad
  tauto

theorem fin15Anchored_clause20824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0849 Fin15AnchoredAtom2936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16550
  ] at hbad
  tauto

theorem fin15Anchored_clause20825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom2936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16550
  ] at hbad
  tauto

theorem fin15Anchored_clause20826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom2936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16550
  ] at hbad
  tauto

theorem fin15Anchored_clause20827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom2936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16550
  ] at hbad
  tauto

theorem fin15Anchored_clause20828 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2936 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom0849 Fin15AnchoredAtom0864
    Fin15AnchoredAtom1000 Fin15AnchoredAtom1220 Fin15AnchoredAtom2936 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16550
  ] at hbad
  tauto

theorem fin15Anchored_clause20829 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2937 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0865 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1221 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0843 Fin15AnchoredAtom0844 Fin15AnchoredAtom0865
    Fin15AnchoredAtom1001 Fin15AnchoredAtom1221 Fin15AnchoredAtom2937 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00806
  ] at hbad
  tauto

theorem fin15Anchored_clause20830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2938 chi ∧
      ¬Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1222 Fin15AnchoredAtom2938 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01318
  ] at hbad
  tauto

theorem fin15Anchored_clause20831 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2938 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0866 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1222 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0843 Fin15AnchoredAtom0845 Fin15AnchoredAtom0866
    Fin15AnchoredAtom1002 Fin15AnchoredAtom1222 Fin15AnchoredAtom2938 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01318
  ] at hbad
  tauto

theorem fin15Anchored_clause20832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2940 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom2940 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04390
  ] at hbad
  tauto

theorem fin15Anchored_clause20833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2941 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom2941 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08486
  ] at hbad
  tauto

theorem fin15Anchored_clause20834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom2943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01574
  ] at hbad
  tauto

theorem fin15Anchored_clause20835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom2943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01574
  ] at hbad
  tauto

theorem fin15Anchored_clause20836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom2943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01574
  ] at hbad
  tauto

theorem fin15Anchored_clause20837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom2943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01574
  ] at hbad
  tauto

theorem fin15Anchored_clause20838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom2943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01574
  ] at hbad
  tauto

theorem fin15Anchored_clause20839 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2943 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom0845 Fin15AnchoredAtom0871
    Fin15AnchoredAtom1007 Fin15AnchoredAtom1227 Fin15AnchoredAtom2943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01574
  ] at hbad
  tauto

theorem fin15Anchored_clause20840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2944 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom2944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02598
  ] at hbad
  tauto

theorem fin15Anchored_clause20841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2944 chi ∧
      ¬Fin15AnchoredAtom1008 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1008 Fin15AnchoredAtom2944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02598
  ] at hbad
  tauto

theorem fin15Anchored_clause20842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2944 chi ∧
      ¬Fin15AnchoredAtom1228 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1228 Fin15AnchoredAtom2944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02598
  ] at hbad
  tauto

theorem fin15Anchored_clause20843 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2944 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0846 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom1008 chi ∧
      Fin15AnchoredAtom1228 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom0846 Fin15AnchoredAtom0872
    Fin15AnchoredAtom1008 Fin15AnchoredAtom1228 Fin15AnchoredAtom2944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02598
  ] at hbad
  tauto

theorem fin15Anchored_clause20844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom2945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04646
  ] at hbad
  tauto

theorem fin15Anchored_clause20845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom2945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04646
  ] at hbad
  tauto

theorem fin15Anchored_clause20846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom2945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04646
  ] at hbad
  tauto

theorem fin15Anchored_clause20847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom2945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04646
  ] at hbad
  tauto

theorem fin15Anchored_clause20848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom2945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04646
  ] at hbad
  tauto

theorem fin15Anchored_clause20849 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2945 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom0847 Fin15AnchoredAtom0873
    Fin15AnchoredAtom1009 Fin15AnchoredAtom1229 Fin15AnchoredAtom2945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04646
  ] at hbad
  tauto

theorem fin15Anchored_clause20850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom2946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08742
  ] at hbad
  tauto

theorem fin15Anchored_clause20851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom2946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08742
  ] at hbad
  tauto

theorem fin15Anchored_clause20852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom2946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08742
  ] at hbad
  tauto

theorem fin15Anchored_clause20853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom2946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08742
  ] at hbad
  tauto

theorem fin15Anchored_clause20854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom2946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08742
  ] at hbad
  tauto

theorem fin15Anchored_clause20855 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2946 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom0848 Fin15AnchoredAtom0874
    Fin15AnchoredAtom1010 Fin15AnchoredAtom1230 Fin15AnchoredAtom2946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08742
  ] at hbad
  tauto

theorem fin15Anchored_clause20856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom2947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16934
  ] at hbad
  tauto

theorem fin15Anchored_clause20857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0849 Fin15AnchoredAtom2947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16934
  ] at hbad
  tauto

theorem fin15Anchored_clause20858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0875 Fin15AnchoredAtom2947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16934
  ] at hbad
  tauto

theorem fin15Anchored_clause20859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom2947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16934
  ] at hbad
  tauto

theorem fin15Anchored_clause20860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1231 Fin15AnchoredAtom2947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16934
  ] at hbad
  tauto

theorem fin15Anchored_clause20861 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2947 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom0849 Fin15AnchoredAtom0875
    Fin15AnchoredAtom1011 Fin15AnchoredAtom1231 Fin15AnchoredAtom2947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16934
  ] at hbad
  tauto

theorem fin15Anchored_clause20862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2948 chi ∧
      ¬Fin15AnchoredAtom0846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0846 Fin15AnchoredAtom2948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03110
  ] at hbad
  tauto

theorem fin15Anchored_clause20863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2948 chi ∧
      ¬Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1232 Fin15AnchoredAtom2948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03110
  ] at hbad
  tauto

end ErdosSzekeres

end
