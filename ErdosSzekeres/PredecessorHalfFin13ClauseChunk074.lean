module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 074. -/

theorem predecessorHalfFin13_clause22583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1905 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom1905 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22584 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1905 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0786 chi ∧
      PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0786 PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom1905 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5388
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22586 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom1906 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22589 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1906 chi ∧
      ¬PredecessorHalfFin13Atom0871 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0871 PredecessorHalfFin13Atom1906 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6412
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22591 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom1907 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3596
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22592 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom1907 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3596
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22594 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0788 PredecessorHalfFin13Atom1907 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3596
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22595 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1907 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom1907 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3596
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22597 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom1908 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22598 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom1908 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22599 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom1908 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22600 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom1908 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1908 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom1908 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22602 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1908 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0789 chi ∧
      PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0789 PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom1908 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5644
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22604 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom1909 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22606 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0790 PredecessorHalfFin13Atom1909 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22607 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1909 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0874 PredecessorHalfFin13Atom1909 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6668
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22610 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom1910 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22611 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom0707 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0707 PredecessorHalfFin13Atom1910 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22612 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0791 PredecessorHalfFin13Atom1910 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22613 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1910 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom1910 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7180
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22615 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom1911 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22616 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom1911 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22617 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom1911 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22618 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0736 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom1911 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22619 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1911 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom1911 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22620 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1911 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0736 chi ∧
      PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0715
    PredecessorHalfFin13Atom0736 PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom1911 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0244
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22621 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom1912 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0372
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22622 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom1912 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0372
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22623 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom1912 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0372
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22624 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0737 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom1912 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0372
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22625 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1912 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom1912 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0372
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22626 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1912 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0737 chi ∧
      PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0716
    PredecessorHalfFin13Atom0737 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom1912 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0372
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22627 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom1913 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0628
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22628 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom1913 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0628
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22629 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom1913 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0628
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22630 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0738 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom1913 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0628
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22631 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1913 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom1913 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0628
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22632 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1913 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0738 chi ∧
      PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0717
    PredecessorHalfFin13Atom0738 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom1913 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0628
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22633 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom1914 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22634 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom1914 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22635 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0718 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0718 PredecessorHalfFin13Atom1914 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22636 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0739 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom1914 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22637 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1914 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom1914 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22638 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1914 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0718 chi ∧
      PredecessorHalfFin13Atom0739 chi ∧
      PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0718
    PredecessorHalfFin13Atom0739 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom1914 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1140
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22639 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom1915 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22640 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom1915 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22641 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0719 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0719 PredecessorHalfFin13Atom1915 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22642 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom1915 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22643 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1915 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom1915 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22644 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1915 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0719 chi ∧
      PredecessorHalfFin13Atom0740 chi ∧
      PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom0719
    PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom1915 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22645 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom1916 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22646 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom1916 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22647 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0720 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0720 PredecessorHalfFin13Atom1916 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22648 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom1916 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22649 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1916 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom1916 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22650 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1916 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0720 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0720
    PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom1916 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4212
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22651 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom1917 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22652 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom1917 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22653 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0721 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0721 PredecessorHalfFin13Atom1917 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22654 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom1917 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22655 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1917 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom1917 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22656 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1917 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0721 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0721
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom1917 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0436
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22657 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom1918 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22658 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom1918 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22659 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0722 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0722 PredecessorHalfFin13Atom1918 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22660 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom1918 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22661 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1918 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom1918 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22662 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1918 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0722 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0722
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom1918 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0692
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22663 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom1919 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22664 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom1919 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22665 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0723 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0723 PredecessorHalfFin13Atom1919 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22666 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom1919 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22667 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1919 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom1919 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22668 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1919 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0723 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0723
    PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom1919 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22669 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom1920 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22670 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom1920 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22671 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0724 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0724 PredecessorHalfFin13Atom1920 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22672 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom1920 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22673 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1920 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom1920 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22674 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1920 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0724 chi ∧
      PredecessorHalfFin13Atom0745 chi ∧
      PredecessorHalfFin13Atom0885 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom0724
    PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom1920 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22675 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom1921 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22676 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom1921 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22677 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0725 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0725 PredecessorHalfFin13Atom1921 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22678 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom1921 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22679 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1921 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom1921 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22680 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1921 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0725 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0725
    PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom1921 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4276
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22681 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom1922 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0820
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22682 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom1922 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0820
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22683 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0726 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0726 PredecessorHalfFin13Atom1922 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0820
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22684 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom1922 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0820
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22685 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1922 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom1922 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0820
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22686 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1922 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0726 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0726
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom1922 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0820
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22687 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom1923 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22688 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom1923 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22689 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0727 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0727 PredecessorHalfFin13Atom1923 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22690 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom1923 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22691 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1923 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom1923 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22692 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1923 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0727 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0727
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom1923 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1332
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22693 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom1924 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22694 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom1924 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22695 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0728 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0728 PredecessorHalfFin13Atom1924 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22696 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom1924 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22697 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1924 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom1924 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2356
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22699 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom1925 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22700 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom1925 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22701 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0729 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0729 PredecessorHalfFin13Atom1925 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22702 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom1925 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22703 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1925 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom1925 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22704 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1925 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0729 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0729
    PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom1925 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4404
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22705 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom1926 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22706 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom1926 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22707 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0730 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0730 PredecessorHalfFin13Atom1926 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22708 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom1926 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22709 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1926 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom1926 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22710 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1926 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0730 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0730
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom1926 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1588
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22711 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom1927 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22712 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom1927 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22713 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0731 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0731 PredecessorHalfFin13Atom1927 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22714 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom1927 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22715 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1927 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom1927 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22716 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1927 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0713 chi ∧
      PredecessorHalfFin13Atom0731 chi ∧
      PredecessorHalfFin13Atom0752 chi ∧
      PredecessorHalfFin13Atom0892 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom0731
    PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom1927 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2612
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22717 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom1928 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22718 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom1928 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22719 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0732 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0732 PredecessorHalfFin13Atom1928 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22720 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom1928 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22721 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1928 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom1928 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4660
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22722 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1928 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0732 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0732
    PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom1928 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4660
  ] at hbad
  tauto

end ErdosSzekeres

end
