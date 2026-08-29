module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 076. -/

theorem predecessorHalfFin13_clause22856 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom1951 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22857 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom1951 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22858 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom1951 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22859 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom1951 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22860 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1951 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom1951 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22861 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom1952 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22862 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom1952 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22863 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom1952 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22864 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom1952 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22865 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1952 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom1952 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22867 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom1953 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22868 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom1953 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22869 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom1953 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22870 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom1953 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22871 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1953 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom1953 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22872 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1953 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom1953 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4756
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22873 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom1954 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22874 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom1954 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22875 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0733 PredecessorHalfFin13Atom1954 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22876 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom1954 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22877 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1954 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom1954 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22878 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1954 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0779 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom1954 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22879 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom1955 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22880 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom1955 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22881 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom1955 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22882 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom1955 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22883 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1955 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom1955 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22884 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1955 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom1955 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22885 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom1956 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6292
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22886 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom1956 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6292
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22887 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0735 PredecessorHalfFin13Atom1956 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6292
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22888 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0781 PredecessorHalfFin13Atom1956 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6292
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22889 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1956 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom1956 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6292
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22891 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom1957 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22892 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom1957 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22893 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom1957 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22894 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom1957 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22895 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1957 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom1957 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22896 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1957 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom1957 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22897 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom1958 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2836
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22898 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom1958 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2836
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22899 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom1958 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2836
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22900 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom1958 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2836
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22901 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1958 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom1958 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2836
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22902 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1958 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0783 chi ∧
      PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom0731
    PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom1958 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2836
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22903 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom1959 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22904 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom1959 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22905 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom1959 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22906 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom1959 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22907 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1959 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom1959 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22908 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1959 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom1959 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4884
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22909 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom1960 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22910 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom1960 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22911 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0733 PredecessorHalfFin13Atom1960 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22912 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom1960 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22913 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1960 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom1960 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22914 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1960 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0925 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom1960 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22915 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom1961 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22916 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom1961 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22917 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom1961 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22918 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom1961 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22919 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1961 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom1961 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22920 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1961 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom1961 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22921 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom1962 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22922 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom1962 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22924 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom0787 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0787 PredecessorHalfFin13Atom1962 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22925 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1962 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0927 PredecessorHalfFin13Atom1962 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6420
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22927 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom1963 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22928 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom1963 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22929 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0733 PredecessorHalfFin13Atom1963 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22930 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom1963 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22931 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1963 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom1963 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22932 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1963 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0788 chi ∧
      PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom1963 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22933 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom1964 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22934 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom1964 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22935 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom1964 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22936 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom1964 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22937 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1964 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom1964 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22938 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1964 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom1964 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22939 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom1965 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22940 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom1965 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22942 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom1965 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22943 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1965 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom1965 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6676
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22945 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0733 PredecessorHalfFin13Atom1966 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22946 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom1966 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22948 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom1966 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22949 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1966 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom1966 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22951 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom1967 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0484
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22952 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom1967 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0484
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22953 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom1967 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0484
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22954 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom1967 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0484
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22955 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1967 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom1967 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0484
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22956 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1967 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0742
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom1967 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0484
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22957 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom1968 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0740
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22958 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom1968 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0740
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22959 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom1968 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0740
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22960 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom1968 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0740
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22961 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1968 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom1968 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0740
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22962 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1968 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0743
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom1968 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0740
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22963 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom1969 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22964 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom1969 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22965 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom1969 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22966 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom1969 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22967 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1969 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom1969 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22968 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1969 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0744
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom1969 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22969 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom1970 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22970 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom1970 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22971 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom1970 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22972 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom1970 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22973 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1970 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0935 PredecessorHalfFin13Atom1970 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22975 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom1971 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22976 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom1971 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22977 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom1971 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22978 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom1971 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22979 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1971 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom1971 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22980 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1971 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0746
    PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom1971 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22981 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom1972 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0868
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22982 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom1972 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0868
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22983 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom1972 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0868
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22984 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom1972 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0868
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22985 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1972 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom1972 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0868
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22986 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1972 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0747
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom1972 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0868
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22987 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom1973 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22988 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom1973 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22989 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom1973 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22990 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom1973 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22991 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1973 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom1973 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1380
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22992 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1973 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0748
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom1973 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1380
  ] at hbad
  tauto

end ErdosSzekeres

end
