module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 082. -/

theorem predecessorHalfFin13_clause23702 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0818 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0818 PredecessorHalfFin13Atom2092 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7192
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23703 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0819 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0819 PredecessorHalfFin13Atom2092 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7192
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23704 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom2092 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7192
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23705 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2092 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom2092 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7192
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23707 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom2093 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23708 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom2093 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23709 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom2093 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23710 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom2093 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23711 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2093 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom2093 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23712 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2093 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0826
    PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom2093 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23713 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom2094 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23714 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom2094 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23715 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom2094 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23716 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom2094 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23717 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2094 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom2094 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23718 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2094 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0827
    PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom2094 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23719 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom2095 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23720 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom2095 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23721 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom2095 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23722 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom2095 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23723 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2095 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom2095 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23724 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2095 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0828
    PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom2095 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23725 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom2096 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23726 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom2096 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23727 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom2096 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23728 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom2096 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23729 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2096 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0935 PredecessorHalfFin13Atom2096 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23731 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0820 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom2097 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23732 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom2097 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23733 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom2097 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23734 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom2097 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23735 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2097 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom2097 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23736 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2097 chi ∧
      PredecessorHalfFin13Atom0820 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0820 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0830
    PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom2097 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23737 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom2098 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23738 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom2098 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23739 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom2098 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23740 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom2098 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23741 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2098 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom2098 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23742 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2098 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0831
    PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom2098 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23743 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom2099 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1384
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23744 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom2099 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1384
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23745 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom2099 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1384
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23746 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom2099 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1384
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23747 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2099 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom2099 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1384
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23748 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2099 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0832
    PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom2099 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1384
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23749 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom2100 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23750 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom2100 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23751 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom2100 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23752 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom2100 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23753 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2100 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom2100 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2408
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23755 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0821 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom2101 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23756 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom2101 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23757 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom2101 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23758 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom2101 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23759 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2101 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom2101 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23760 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2101 chi ∧
      PredecessorHalfFin13Atom0821 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0821 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom2101 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23761 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom2102 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1640
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23762 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom2102 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1640
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23763 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom2102 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1640
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23764 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom2102 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1640
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23765 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2102 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom2102 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1640
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23766 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2102 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0835
    PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom2102 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1640
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23767 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom2103 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23768 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom2103 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23770 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom2103 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23771 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2103 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom2103 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23772 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2103 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0824 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom0836
    PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom2103 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2664
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23773 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0822 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom2104 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23774 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom2104 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23775 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom2104 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23776 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom2104 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23777 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2104 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom2104 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23778 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2104 chi ∧
      PredecessorHalfFin13Atom0822 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0822 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom2104 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23779 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom2105 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23780 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom2105 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23781 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom2105 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23782 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom2105 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23783 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2105 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom2105 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3176
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23785 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0823 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom2106 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23786 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom2106 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23787 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom2106 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23788 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom2106 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23789 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2106 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom2106 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23790 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2106 chi ∧
      PredecessorHalfFin13Atom0823 chi ∧
      PredecessorHalfFin13Atom0825 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0823 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom2106 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5224
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23791 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom2107 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23792 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom2107 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23793 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0840 PredecessorHalfFin13Atom2107 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23794 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0855 PredecessorHalfFin13Atom2107 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23795 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2107 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0946 PredecessorHalfFin13Atom2107 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23797 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom2108 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23798 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom2108 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23799 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom2108 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23800 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom2108 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23801 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2108 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom2108 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23802 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2108 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0831
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom2108 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23803 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom2109 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23804 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom2109 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23805 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom2109 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23806 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom2109 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23807 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2109 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom2109 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23808 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2109 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0832
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom2109 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23809 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom2110 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23810 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom2110 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23811 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom2110 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23812 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom2110 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23813 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2110 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom2110 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23814 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2110 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0833
    PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom2110 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23815 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom2111 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23816 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom2111 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23817 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom2111 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23818 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom2111 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23819 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2111 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom2111 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23820 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2111 chi ∧
      PredecessorHalfFin13Atom0826 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0834
    PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom2111 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4520
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23821 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom2112 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23822 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom2112 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23823 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom2112 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23824 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom2112 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23825 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2112 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom2112 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23826 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2112 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0835
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom2112 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23827 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom2113 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23828 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom2113 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23829 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom2113 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23830 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom2113 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23831 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2113 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom2113 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23832 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2113 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0836
    PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom2113 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23833 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom2114 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23834 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom2114 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23835 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom2114 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4776
  ] at hbad
  tauto

end ErdosSzekeres

end
