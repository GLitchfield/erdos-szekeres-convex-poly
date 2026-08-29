module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 077. -/

theorem predecessorHalfFin13_clause22993 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom1974 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22994 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom1974 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22995 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom1974 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22996 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom1974 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22997 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1974 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom1974 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22999 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom1975 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23000 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom1975 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23001 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom1975 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23002 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom1975 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23003 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1975 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom1975 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23004 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1975 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom1975 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23005 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom1976 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23006 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom1976 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23007 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom1976 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23008 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom1976 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23009 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1976 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom1976 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23010 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1976 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom1976 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1636
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23011 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom1977 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23012 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom1977 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23013 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom1977 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23014 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom1977 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23015 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1977 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom1977 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23017 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom1978 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23018 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom1978 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23019 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom1978 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23020 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom1978 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23021 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1978 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom1978 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23022 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1978 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom1978 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4708
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23023 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom1979 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23024 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom1979 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23025 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom1979 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23026 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0769 PredecessorHalfFin13Atom1979 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23027 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1979 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom1979 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23029 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom1980 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23030 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom1980 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23031 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom1980 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23032 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom1980 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23033 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1980 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom1980 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23034 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1980 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom1980 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23035 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom1981 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23036 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom1981 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23037 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0756 PredecessorHalfFin13Atom1981 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23038 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0771 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0771 PredecessorHalfFin13Atom1981 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23039 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1981 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0946 PredecessorHalfFin13Atom1981 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23041 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom1982 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23042 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom1982 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23043 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom1982 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23044 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom1982 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23045 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1982 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom1982 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23046 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1982 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0747
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom1982 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0932
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23047 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom1983 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23048 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom1983 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23049 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom1983 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23050 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom1983 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23051 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1983 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom1983 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23052 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1983 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0748
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom1983 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1444
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23053 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom1984 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23054 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom1984 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23055 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom1984 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23056 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom1984 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23057 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1984 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom1984 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23058 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1984 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom0749
    PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom1984 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23059 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom1985 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4516
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23060 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom1985 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4516
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23061 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom1985 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4516
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23062 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom1985 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4516
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23063 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1985 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom1985 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4516
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23064 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1985 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0750
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom1985 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4516
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23065 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom1986 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23066 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom1986 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23067 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom1986 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23068 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0776 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom1986 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23069 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1986 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom1986 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23070 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1986 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0776 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0776 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom1986 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1700
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23071 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom1987 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23072 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom1987 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23073 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom1987 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23074 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0777 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0777 PredecessorHalfFin13Atom1987 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23075 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1987 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom1987 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23077 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom1988 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4772
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23078 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom1988 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4772
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23079 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom1988 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4772
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23080 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0778 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom1988 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4772
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23081 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1988 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom1988 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4772
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23082 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1988 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0778 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0778 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom1988 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4772
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23083 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom1989 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23085 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom1989 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23086 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom0779 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0779 PredecessorHalfFin13Atom1989 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23087 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1989 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom1989 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23089 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom1990 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23090 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom1990 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23091 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom1990 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23092 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0780 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom1990 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23093 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1990 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom1990 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23094 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1990 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0780 chi ∧
      PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0780 PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom1990 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5284
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23095 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom1991 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23096 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom1991 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23098 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom0781 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0781 PredecessorHalfFin13Atom1991 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23099 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1991 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0956 PredecessorHalfFin13Atom1991 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23101 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom1992 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23102 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom1992 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23103 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom1992 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23104 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0782 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom1992 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23105 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1992 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom1992 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23106 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1992 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0782 chi ∧
      PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0751
    PredecessorHalfFin13Atom0782 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom1992 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1828
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23107 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom1993 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23108 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom1993 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23109 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom1993 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23110 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0783 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0783 PredecessorHalfFin13Atom1993 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23111 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1993 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom1993 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23113 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom1994 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4900
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23114 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom1994 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4900
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23115 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom1994 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4900
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23116 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0784 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom1994 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4900
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23117 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1994 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom1994 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4900
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23118 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1994 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0784 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0753
    PredecessorHalfFin13Atom0784 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom1994 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4900
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23119 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom1995 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23120 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom1995 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23121 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom1995 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23122 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0785 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom1995 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23123 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1995 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom1995 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23124 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1995 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0749 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0785 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom0754
    PredecessorHalfFin13Atom0785 PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom1995 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23125 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom1996 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23126 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom1996 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23127 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom1996 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23128 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0786 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom1996 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23129 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1996 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom1996 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23130 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1996 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0755
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom1996 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5412
  ] at hbad
  tauto

end ErdosSzekeres

end
