module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 156. -/

theorem fin15Anchored_clause19968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25153
  ] at hbad
  tauto

theorem fin15Anchored_clause19969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25153
  ] at hbad
  tauto

theorem fin15Anchored_clause19970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25153
  ] at hbad
  tauto

theorem fin15Anchored_clause19971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25153
  ] at hbad
  tauto

theorem fin15Anchored_clause19972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2741 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom2741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25153
  ] at hbad
  tauto

theorem fin15Anchored_clause19973 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom0753 Fin15AnchoredAtom0763
    Fin15AnchoredAtom0809 Fin15AnchoredAtom1740 Fin15AnchoredAtom2741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25153
  ] at hbad
  tauto

theorem fin15Anchored_clause19974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07233
  ] at hbad
  tauto

theorem fin15Anchored_clause19975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2742 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom2742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07233
  ] at hbad
  tauto

theorem fin15Anchored_clause19976 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2742 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom0755 Fin15AnchoredAtom0758
    Fin15AnchoredAtom0810 Fin15AnchoredAtom1741 Fin15AnchoredAtom2742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07233
  ] at hbad
  tauto

theorem fin15Anchored_clause19977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom2743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11329
  ] at hbad
  tauto

theorem fin15Anchored_clause19978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11329
  ] at hbad
  tauto

theorem fin15Anchored_clause19979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom0759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0759 Fin15AnchoredAtom2743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11329
  ] at hbad
  tauto

theorem fin15Anchored_clause19980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11329
  ] at hbad
  tauto

theorem fin15Anchored_clause19981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2743 chi ∧
      ¬Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1742 Fin15AnchoredAtom2743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11329
  ] at hbad
  tauto

theorem fin15Anchored_clause19982 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2743 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom0756 Fin15AnchoredAtom0759
    Fin15AnchoredAtom0811 Fin15AnchoredAtom1742 Fin15AnchoredAtom2743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11329
  ] at hbad
  tauto

theorem fin15Anchored_clause19983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom2744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19521
  ] at hbad
  tauto

theorem fin15Anchored_clause19984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19521
  ] at hbad
  tauto

theorem fin15Anchored_clause19985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom0760 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0760 Fin15AnchoredAtom2744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19521
  ] at hbad
  tauto

theorem fin15Anchored_clause19986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom0812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0812 Fin15AnchoredAtom2744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19521
  ] at hbad
  tauto

theorem fin15Anchored_clause19987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2744 chi ∧
      ¬Fin15AnchoredAtom1743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1743 Fin15AnchoredAtom2744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19521
  ] at hbad
  tauto

theorem fin15Anchored_clause19988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2744 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom0757 Fin15AnchoredAtom0760
    Fin15AnchoredAtom0812 Fin15AnchoredAtom1743 Fin15AnchoredAtom2744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19521
  ] at hbad
  tauto

theorem fin15Anchored_clause19989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2745 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13377
  ] at hbad
  tauto

theorem fin15Anchored_clause19990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2745 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13377
  ] at hbad
  tauto

theorem fin15Anchored_clause19991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2745 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13377
  ] at hbad
  tauto

theorem fin15Anchored_clause19992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2745 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13377
  ] at hbad
  tauto

theorem fin15Anchored_clause19993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2745 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom2745 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13377
  ] at hbad
  tauto

theorem fin15Anchored_clause19994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom0756 Fin15AnchoredAtom0761
    Fin15AnchoredAtom0813 Fin15AnchoredAtom1744 Fin15AnchoredAtom2745 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13377
  ] at hbad
  tauto

theorem fin15Anchored_clause19995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21569
  ] at hbad
  tauto

theorem fin15Anchored_clause19996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21569
  ] at hbad
  tauto

theorem fin15Anchored_clause19997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21569
  ] at hbad
  tauto

theorem fin15Anchored_clause19998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21569
  ] at hbad
  tauto

theorem fin15Anchored_clause19999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2746 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom2746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21569
  ] at hbad
  tauto

theorem fin15Anchored_clause20000 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom0757 Fin15AnchoredAtom0762
    Fin15AnchoredAtom0814 Fin15AnchoredAtom1745 Fin15AnchoredAtom2746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21569
  ] at hbad
  tauto

theorem fin15Anchored_clause20001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25665
  ] at hbad
  tauto

theorem fin15Anchored_clause20002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25665
  ] at hbad
  tauto

theorem fin15Anchored_clause20003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25665
  ] at hbad
  tauto

theorem fin15Anchored_clause20004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25665
  ] at hbad
  tauto

theorem fin15Anchored_clause20005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2747 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom2747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25665
  ] at hbad
  tauto

theorem fin15Anchored_clause20006 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom0757 Fin15AnchoredAtom0763
    Fin15AnchoredAtom0815 Fin15AnchoredAtom1746 Fin15AnchoredAtom2747 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25665
  ] at hbad
  tauto

theorem fin15Anchored_clause20007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom0758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0758 Fin15AnchoredAtom2748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14401
  ] at hbad
  tauto

theorem fin15Anchored_clause20008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14401
  ] at hbad
  tauto

theorem fin15Anchored_clause20009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0816 Fin15AnchoredAtom2748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14401
  ] at hbad
  tauto

theorem fin15Anchored_clause20010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2748 chi ∧
      ¬Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1747 Fin15AnchoredAtom2748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14401
  ] at hbad
  tauto

theorem fin15Anchored_clause20011 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2748 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0758 Fin15AnchoredAtom0759 Fin15AnchoredAtom0761
    Fin15AnchoredAtom0816 Fin15AnchoredAtom1747 Fin15AnchoredAtom2748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14401
  ] at hbad
  tauto

theorem fin15Anchored_clause20012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2749 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2749 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22593
  ] at hbad
  tauto

theorem fin15Anchored_clause20013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2749 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0817 chi ∧
      Fin15AnchoredAtom1748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0758 Fin15AnchoredAtom0760 Fin15AnchoredAtom0762
    Fin15AnchoredAtom0817 Fin15AnchoredAtom1748 Fin15AnchoredAtom2749 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22593
  ] at hbad
  tauto

theorem fin15Anchored_clause20014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28737
  ] at hbad
  tauto

theorem fin15Anchored_clause20015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28737
  ] at hbad
  tauto

theorem fin15Anchored_clause20016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28737
  ] at hbad
  tauto

theorem fin15Anchored_clause20017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28737
  ] at hbad
  tauto

theorem fin15Anchored_clause20018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2751 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom2751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28737
  ] at hbad
  tauto

theorem fin15Anchored_clause20019 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom0762 Fin15AnchoredAtom0763
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1750 Fin15AnchoredAtom2751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28737
  ] at hbad
  tauto

theorem fin15Anchored_clause20020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom2752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01921
  ] at hbad
  tauto

theorem fin15Anchored_clause20021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom2752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01921
  ] at hbad
  tauto

theorem fin15Anchored_clause20022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01921
  ] at hbad
  tauto

theorem fin15Anchored_clause20023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom2752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01921
  ] at hbad
  tauto

theorem fin15Anchored_clause20024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2752 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom2752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01921
  ] at hbad
  tauto

theorem fin15Anchored_clause20025 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom0765 Fin15AnchoredAtom0770
    Fin15AnchoredAtom0785 Fin15AnchoredAtom1751 Fin15AnchoredAtom2752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01921
  ] at hbad
  tauto

theorem fin15Anchored_clause20026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom2754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04993
  ] at hbad
  tauto

theorem fin15Anchored_clause20027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom2754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04993
  ] at hbad
  tauto

theorem fin15Anchored_clause20028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04993
  ] at hbad
  tauto

theorem fin15Anchored_clause20029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom2754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04993
  ] at hbad
  tauto

theorem fin15Anchored_clause20030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2754 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom2754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04993
  ] at hbad
  tauto

theorem fin15Anchored_clause20031 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom0767 Fin15AnchoredAtom0772
    Fin15AnchoredAtom0787 Fin15AnchoredAtom1753 Fin15AnchoredAtom2754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04993
  ] at hbad
  tauto

theorem fin15Anchored_clause20032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom2755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09089
  ] at hbad
  tauto

theorem fin15Anchored_clause20033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09089
  ] at hbad
  tauto

theorem fin15Anchored_clause20034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom2755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09089
  ] at hbad
  tauto

theorem fin15Anchored_clause20035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2755 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom2755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09089
  ] at hbad
  tauto

theorem fin15Anchored_clause20036 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom0768 Fin15AnchoredAtom0773
    Fin15AnchoredAtom0788 Fin15AnchoredAtom1754 Fin15AnchoredAtom2755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09089
  ] at hbad
  tauto

theorem fin15Anchored_clause20037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom2756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17281
  ] at hbad
  tauto

theorem fin15Anchored_clause20038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0769 Fin15AnchoredAtom2756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17281
  ] at hbad
  tauto

theorem fin15Anchored_clause20039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17281
  ] at hbad
  tauto

theorem fin15Anchored_clause20040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0789 Fin15AnchoredAtom2756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17281
  ] at hbad
  tauto

theorem fin15Anchored_clause20041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2756 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1755 Fin15AnchoredAtom2756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17281
  ] at hbad
  tauto

theorem fin15Anchored_clause20042 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom0769 Fin15AnchoredAtom0774
    Fin15AnchoredAtom0789 Fin15AnchoredAtom1755 Fin15AnchoredAtom2756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17281
  ] at hbad
  tauto

theorem fin15Anchored_clause20043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom2758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05505
  ] at hbad
  tauto

theorem fin15Anchored_clause20044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom2758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05505
  ] at hbad
  tauto

theorem fin15Anchored_clause20045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05505
  ] at hbad
  tauto

theorem fin15Anchored_clause20046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom2758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05505
  ] at hbad
  tauto

theorem fin15Anchored_clause20047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2758 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom2758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05505
  ] at hbad
  tauto

theorem fin15Anchored_clause20048 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom0767 Fin15AnchoredAtom0776
    Fin15AnchoredAtom0791 Fin15AnchoredAtom1757 Fin15AnchoredAtom2758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05505
  ] at hbad
  tauto

theorem fin15Anchored_clause20049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom2759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09601
  ] at hbad
  tauto

theorem fin15Anchored_clause20050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0768 Fin15AnchoredAtom2759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09601
  ] at hbad
  tauto

theorem fin15Anchored_clause20051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09601
  ] at hbad
  tauto

theorem fin15Anchored_clause20052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09601
  ] at hbad
  tauto

theorem fin15Anchored_clause20053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2759 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom2759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09601
  ] at hbad
  tauto

theorem fin15Anchored_clause20054 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom0768 Fin15AnchoredAtom0777
    Fin15AnchoredAtom0792 Fin15AnchoredAtom1758 Fin15AnchoredAtom2759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09601
  ] at hbad
  tauto

theorem fin15Anchored_clause20055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom2760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17793
  ] at hbad
  tauto

theorem fin15Anchored_clause20056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0769 Fin15AnchoredAtom2760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17793
  ] at hbad
  tauto

theorem fin15Anchored_clause20057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17793
  ] at hbad
  tauto

theorem fin15Anchored_clause20058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0793 Fin15AnchoredAtom2760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17793
  ] at hbad
  tauto

theorem fin15Anchored_clause20059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2760 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1759 Fin15AnchoredAtom2760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17793
  ] at hbad
  tauto

theorem fin15Anchored_clause20060 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom0769 Fin15AnchoredAtom0778
    Fin15AnchoredAtom0793 Fin15AnchoredAtom1759 Fin15AnchoredAtom2760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17793
  ] at hbad
  tauto

theorem fin15Anchored_clause20061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom2764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12673
  ] at hbad
  tauto

theorem fin15Anchored_clause20062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0768 Fin15AnchoredAtom2764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12673
  ] at hbad
  tauto

theorem fin15Anchored_clause20063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12673
  ] at hbad
  tauto

theorem fin15Anchored_clause20064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12673
  ] at hbad
  tauto

theorem fin15Anchored_clause20065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2764 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom2764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12673
  ] at hbad
  tauto

theorem fin15Anchored_clause20066 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom0768 Fin15AnchoredAtom0782
    Fin15AnchoredAtom0797 Fin15AnchoredAtom1763 Fin15AnchoredAtom2764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12673
  ] at hbad
  tauto

theorem fin15Anchored_clause20067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom2765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20865
  ] at hbad
  tauto

theorem fin15Anchored_clause20068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0769 Fin15AnchoredAtom2765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20865
  ] at hbad
  tauto

theorem fin15Anchored_clause20069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20865
  ] at hbad
  tauto

theorem fin15Anchored_clause20070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0798 Fin15AnchoredAtom2765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20865
  ] at hbad
  tauto

theorem fin15Anchored_clause20071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2765 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1764 Fin15AnchoredAtom2765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20865
  ] at hbad
  tauto

theorem fin15Anchored_clause20072 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom0769 Fin15AnchoredAtom0783
    Fin15AnchoredAtom0798 Fin15AnchoredAtom1764 Fin15AnchoredAtom2765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20865
  ] at hbad
  tauto

theorem fin15Anchored_clause20073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0768 Fin15AnchoredAtom2766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24961
  ] at hbad
  tauto

theorem fin15Anchored_clause20074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0769 Fin15AnchoredAtom2766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24961
  ] at hbad
  tauto

theorem fin15Anchored_clause20075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24961
  ] at hbad
  tauto

theorem fin15Anchored_clause20076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0799 Fin15AnchoredAtom2766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24961
  ] at hbad
  tauto

theorem fin15Anchored_clause20077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2766 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1765 Fin15AnchoredAtom2766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24961
  ] at hbad
  tauto

theorem fin15Anchored_clause20078 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0768 Fin15AnchoredAtom0769 Fin15AnchoredAtom0784
    Fin15AnchoredAtom0799 Fin15AnchoredAtom1765 Fin15AnchoredAtom2766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24961
  ] at hbad
  tauto

theorem fin15Anchored_clause20079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2767 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03713
  ] at hbad
  tauto

theorem fin15Anchored_clause20080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom2767 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03713
  ] at hbad
  tauto

theorem fin15Anchored_clause20081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2767 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03713
  ] at hbad
  tauto

theorem fin15Anchored_clause20082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2767 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03713
  ] at hbad
  tauto

theorem fin15Anchored_clause20083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2767 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom2767 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03713
  ] at hbad
  tauto

theorem fin15Anchored_clause20084 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2767 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom0771 Fin15AnchoredAtom0775
    Fin15AnchoredAtom0800 Fin15AnchoredAtom1766 Fin15AnchoredAtom2767 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03713
  ] at hbad
  tauto

theorem fin15Anchored_clause20085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2768 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05761
  ] at hbad
  tauto

theorem fin15Anchored_clause20086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2768 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05761
  ] at hbad
  tauto

theorem fin15Anchored_clause20087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2768 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05761
  ] at hbad
  tauto

theorem fin15Anchored_clause20088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2768 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05761
  ] at hbad
  tauto

theorem fin15Anchored_clause20089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2768 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom2768 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05761
  ] at hbad
  tauto

theorem fin15Anchored_clause20090 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom0772 Fin15AnchoredAtom0776
    Fin15AnchoredAtom0801 Fin15AnchoredAtom1767 Fin15AnchoredAtom2768 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05761
  ] at hbad
  tauto

theorem fin15Anchored_clause20091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09857
  ] at hbad
  tauto

theorem fin15Anchored_clause20092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09857
  ] at hbad
  tauto

theorem fin15Anchored_clause20093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09857
  ] at hbad
  tauto

theorem fin15Anchored_clause20094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09857
  ] at hbad
  tauto

theorem fin15Anchored_clause20095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2769 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom2769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09857
  ] at hbad
  tauto

end ErdosSzekeres

end
