module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 075. -/

theorem predecessorHalfFin13_clause22723 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom1929 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22724 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom1929 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22725 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0733 PredecessorHalfFin13Atom1929 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22726 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom1929 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22727 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1929 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom1929 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22728 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1929 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0733 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0894 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom0733
    PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom1929 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22729 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom1930 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22730 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom1930 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22731 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom1930 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22732 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom1930 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22733 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1930 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom1930 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22734 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1930 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom1930 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5172
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22735 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom1931 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22736 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom1931 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22737 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0735 PredecessorHalfFin13Atom1931 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22738 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0756 PredecessorHalfFin13Atom1931 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22739 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1931 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0896 PredecessorHalfFin13Atom1931 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22741 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom1932 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22742 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom1932 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22743 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom1932 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22744 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom1932 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22745 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1932 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom1932 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22746 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1932 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0721
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom1932 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0468
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22747 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom1933 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22748 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom1933 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22749 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom1933 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22750 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom1933 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22751 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1933 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom1933 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22752 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1933 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0722
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom1933 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0724
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22753 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom1934 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22754 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom1934 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22755 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom1934 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22756 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom1934 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22757 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1934 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom1934 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22758 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1934 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0723
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom1934 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1236
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22759 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom1935 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22760 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom1935 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22761 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom1935 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22762 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom1935 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22763 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1935 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom1935 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22764 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1935 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0760 chi ∧
      PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom0724
    PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom1935 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2260
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22765 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom1936 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22766 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom1936 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22767 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom1936 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22768 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom1936 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22769 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1936 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom1936 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22770 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1936 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom1936 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4308
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22771 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom1937 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22772 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom1937 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22773 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom1937 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22774 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom1937 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22775 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1937 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom1937 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22776 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1937 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0726
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom1937 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0852
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22777 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom1938 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22778 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom1938 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22779 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom1938 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22780 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0763 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom1938 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22781 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1938 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom1938 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22782 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1938 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0763 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0763 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom1938 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1364
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22783 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom1939 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22784 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom1939 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22785 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom1939 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22786 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0764 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0764 PredecessorHalfFin13Atom1939 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22787 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1939 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom1939 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22789 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom1940 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22790 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom1940 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22791 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom1940 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22792 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0765 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom1940 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22793 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1940 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom1940 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22794 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1940 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0765 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0765 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom1940 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22795 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom1941 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22796 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom1941 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22797 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom1941 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22798 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0766 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom1941 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22799 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1941 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom1941 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22800 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1941 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0766 chi ∧
      PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0766 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom1941 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1620
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22801 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom1942 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22802 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom1942 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22803 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom1942 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22804 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0767 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0767 PredecessorHalfFin13Atom1942 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22805 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1942 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom1942 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22807 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom1943 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22808 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom1943 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22809 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom1943 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22810 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0768 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom1943 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22811 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1943 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom1943 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22812 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1943 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0768 chi ∧
      PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0768 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom1943 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22813 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom1944 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22814 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom1944 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22815 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0733 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0733 PredecessorHalfFin13Atom1944 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22816 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0769 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0769 PredecessorHalfFin13Atom1944 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22817 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1944 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom1944 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22819 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom1945 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22820 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom1945 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22821 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0734 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0734 PredecessorHalfFin13Atom1945 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22822 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0770 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom1945 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22823 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1945 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom1945 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22824 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1945 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0734 chi ∧
      PredecessorHalfFin13Atom0770 chi ∧
      PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom0734
    PredecessorHalfFin13Atom0770 PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom1945 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22825 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom1946 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22826 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom1946 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22827 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0735 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0735 PredecessorHalfFin13Atom1946 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22828 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0771 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0771 PredecessorHalfFin13Atom1946 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22829 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1946 chi ∧
      ¬PredecessorHalfFin13Atom0911 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0911 PredecessorHalfFin13Atom1946 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22831 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom1947 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0916
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22832 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom1947 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0916
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22833 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom1947 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0916
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22834 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0772 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom1947 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0916
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22835 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1947 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom1947 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0916
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22836 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1947 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0772 chi ∧
      PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom0726
    PredecessorHalfFin13Atom0772 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom1947 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0916
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22837 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom1948 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22838 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom1948 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22839 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom1948 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22840 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0773 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom1948 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22841 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1948 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom1948 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22842 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1948 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0773 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0773 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom1948 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22843 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom1949 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22844 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom1949 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22845 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom1949 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22846 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0774 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom1949 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22847 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1949 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom1949 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22848 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1949 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0728 chi ∧
      PredecessorHalfFin13Atom0774 chi ∧
      PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom0728
    PredecessorHalfFin13Atom0774 PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom1949 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2452
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22849 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom1950 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22850 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom1950 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22851 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom1950 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22852 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0775 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom1950 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22853 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1950 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom1950 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22854 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1950 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0775 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0775 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom1950 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4500
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22855 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1951 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom1951 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1684
  ] at hbad
  tauto

end ErdosSzekeres

end
