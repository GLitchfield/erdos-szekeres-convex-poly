module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 081. -/

theorem predecessorHalfFin13_clause23567 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2069 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom2069 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23568 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2069 chi ∧
      PredecessorHalfFin13Atom0801 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom2069 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23569 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom2070 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3160
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23570 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom2070 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3160
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23571 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom2070 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3160
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23572 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom2070 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3160
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23573 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2070 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom2070 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3160
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23575 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0802 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom2071 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23576 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom2071 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23577 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom2071 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23578 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom2071 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23579 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2071 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom2071 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23580 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2071 chi ∧
      PredecessorHalfFin13Atom0802 chi ∧
      PredecessorHalfFin13Atom0804 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0802 PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom2071 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0803 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0803 PredecessorHalfFin13Atom2072 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23582 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0804 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0804 PredecessorHalfFin13Atom2072 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0819 PredecessorHalfFin13Atom2072 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23584 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0855 PredecessorHalfFin13Atom2072 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23585 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2072 chi ∧
      ¬PredecessorHalfFin13Atom0911 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0911 PredecessorHalfFin13Atom2072 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23587 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom2073 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23588 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom2073 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23589 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom2073 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23590 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom2073 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23591 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2073 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom2073 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23592 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2073 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0810
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom2073 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23593 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom2074 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23594 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom2074 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23595 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom2074 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23596 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom2074 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23597 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2074 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom2074 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23598 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2074 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0811
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom2074 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23599 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom2075 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23600 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom2075 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom2075 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23602 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom2075 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23603 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2075 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom2075 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23605 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0805 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom2076 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23606 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom2076 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23607 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom2076 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23608 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom2076 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23609 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2076 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom2076 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23610 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2076 chi ∧
      PredecessorHalfFin13Atom0805 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0805 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0813
    PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom2076 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23611 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom2077 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1688
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23612 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom2077 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1688
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23613 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom2077 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1688
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23614 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom2077 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1688
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23615 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2077 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom2077 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1688
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23616 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2077 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom2077 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1688
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23617 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom2078 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23618 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom2078 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23619 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom2078 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23620 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom2078 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23621 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2078 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom2078 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23622 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2078 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom2078 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23623 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0806 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom2079 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23624 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom2079 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23625 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom2079 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23626 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom2079 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23627 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2079 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom2079 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23628 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2079 chi ∧
      PredecessorHalfFin13Atom0806 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0806 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom2079 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23629 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom2080 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23630 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom2080 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23631 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom2080 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23632 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom2080 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23633 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2080 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom2080 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23635 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0807 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom2081 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23636 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom2081 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23637 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom2081 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23638 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom2081 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23639 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2081 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom2081 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23640 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2081 chi ∧
      PredecessorHalfFin13Atom0807 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0807 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom2081 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23641 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0808 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom2082 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23642 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0809 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom2082 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23643 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0819 PredecessorHalfFin13Atom2082 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23644 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0865 PredecessorHalfFin13Atom2082 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23645 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2082 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom2082 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23646 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2082 chi ∧
      PredecessorHalfFin13Atom0808 chi ∧
      PredecessorHalfFin13Atom0809 chi ∧
      PredecessorHalfFin13Atom0819 chi ∧
      PredecessorHalfFin13Atom0865 chi ∧
      PredecessorHalfFin13Atom0921 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0808 PredecessorHalfFin13Atom0809 PredecessorHalfFin13Atom0819
    PredecessorHalfFin13Atom0865 PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom2082 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23647 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom2083 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23648 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom2083 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23649 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom2083 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23650 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom2083 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23651 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2083 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom2083 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23652 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2083 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0814
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom2083 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23653 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom2084 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23654 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom2084 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23655 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom2084 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23656 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom2084 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23657 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2084 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom2084 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23658 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2084 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0815
    PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom2084 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23659 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0810 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom2085 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23660 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom2085 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23661 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom2085 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23662 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom2085 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23663 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2085 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom2085 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23664 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2085 chi ∧
      PredecessorHalfFin13Atom0810 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0810 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0816
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom2085 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23665 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom2086 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23666 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom2086 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23667 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom2086 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23668 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom2086 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23669 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2086 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom2086 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23670 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2086 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0812 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0925 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom2086 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23671 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0811 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom2087 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23672 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom2087 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23673 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom2087 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23674 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom2087 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23675 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2087 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom2087 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23676 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2087 chi ∧
      PredecessorHalfFin13Atom0811 chi ∧
      PredecessorHalfFin13Atom0813 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0811 PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom2087 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23677 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom0812 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0812 PredecessorHalfFin13Atom2088 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23678 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom0813 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0813 PredecessorHalfFin13Atom2088 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23680 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom0871 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0871 PredecessorHalfFin13Atom2088 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23681 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2088 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0927 PredecessorHalfFin13Atom2088 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23683 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom2089 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3608
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23684 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom2089 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3608
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23685 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom2089 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3608
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23686 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom2089 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3608
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23687 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2089 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom2089 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3608
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23688 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2089 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0815 chi ∧
      PredecessorHalfFin13Atom0817 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom0817
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom2089 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3608
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23689 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0814 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom2090 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23690 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom2090 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23691 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom2090 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23692 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom2090 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23693 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2090 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom2090 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23694 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2090 chi ∧
      PredecessorHalfFin13Atom0814 chi ∧
      PredecessorHalfFin13Atom0816 chi ∧
      PredecessorHalfFin13Atom0818 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0814 PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom0818
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom2090 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23695 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0815 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0815 PredecessorHalfFin13Atom2091 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23696 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0816 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0816 PredecessorHalfFin13Atom2091 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23697 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0819 PredecessorHalfFin13Atom2091 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23698 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0874 PredecessorHalfFin13Atom2091 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23699 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2091 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom2091 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23701 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0817 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0817 PredecessorHalfFin13Atom2092 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7192
  ] at hbad
  tauto

end ErdosSzekeres

end
