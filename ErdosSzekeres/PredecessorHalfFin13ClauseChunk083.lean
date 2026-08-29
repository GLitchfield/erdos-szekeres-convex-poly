module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 083. -/

theorem predecessorHalfFin13_clause23836 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom2114 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23837 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2114 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom2114 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23838 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2114 chi ∧
      PredecessorHalfFin13Atom0827 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom2114 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4776
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23839 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom2115 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23840 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom2115 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23841 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom2115 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23842 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom2115 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23843 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2115 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom2115 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23844 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2115 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0829 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0954 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom2115 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23845 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom2116 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23846 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom2116 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23847 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom2116 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23848 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom2116 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23849 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2116 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom2116 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23850 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2116 chi ∧
      PredecessorHalfFin13Atom0828 chi ∧
      PredecessorHalfFin13Atom0830 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom2116 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23852 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom2117 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23854 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0865 PredecessorHalfFin13Atom2117 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23855 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2117 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0956 PredecessorHalfFin13Atom2117 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6312
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23857 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom2118 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23858 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom2118 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23859 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom2118 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23860 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom2118 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23861 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2118 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom2118 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23862 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2118 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0835
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom2118 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1832
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23863 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom2119 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23864 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom2119 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23865 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom2119 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23866 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom2119 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23867 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2119 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom2119 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2856
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23869 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom2120 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23870 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom2120 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23871 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom2120 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23872 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom2120 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23873 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2120 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom2120 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23874 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2120 chi ∧
      PredecessorHalfFin13Atom0831 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0837
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom2120 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4904
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23875 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom2121 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23876 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom2121 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23877 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom2121 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23878 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom2121 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23879 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2121 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom2121 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23880 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2121 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0833 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom2121 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3368
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23881 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom2122 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23882 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom2122 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23883 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom2122 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23884 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom2122 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23885 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2122 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom2122 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23886 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2122 chi ∧
      PredecessorHalfFin13Atom0832 chi ∧
      PredecessorHalfFin13Atom0834 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom2122 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23888 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom2123 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23889 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0840 PredecessorHalfFin13Atom2123 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23890 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom0871 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0871 PredecessorHalfFin13Atom2123 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23891 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2123 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0962 PredecessorHalfFin13Atom2123 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6440
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23893 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom2124 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23894 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom2124 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23895 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom2124 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23896 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom2124 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23897 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2124 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom2124 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23898 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2124 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0836 chi ∧
      PredecessorHalfFin13Atom0838 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom0838
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom2124 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3624
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23899 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom2125 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23900 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom2125 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23901 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom2125 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23902 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom2125 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23903 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2125 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom2125 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23904 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2125 chi ∧
      PredecessorHalfFin13Atom0835 chi ∧
      PredecessorHalfFin13Atom0837 chi ∧
      PredecessorHalfFin13Atom0839 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom0839
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom2125 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23905 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom2126 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23906 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom2126 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23907 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0840 PredecessorHalfFin13Atom2126 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23908 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0874 PredecessorHalfFin13Atom2126 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23909 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2126 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom2126 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6696
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23911 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom2127 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23912 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom2127 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23914 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom2127 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23915 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2127 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom2127 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7208
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23917 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom2128 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23918 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom2128 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23919 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom2128 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23920 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom2128 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23921 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2128 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2128 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23922 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2128 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0846
    PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2128 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0968
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23923 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom2129 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23924 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom2129 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23925 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom2129 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23926 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom2129 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23927 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2129 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2129 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23928 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2129 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0847
    PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2129 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23929 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom2130 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23930 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom2130 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23931 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom2130 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23932 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom2130 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23933 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2130 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2130 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23934 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2130 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0848
    PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2130 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2504
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23935 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom2131 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4552
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23936 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom2131 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4552
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23937 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom2131 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4552
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23938 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom2131 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4552
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23939 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2131 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2131 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4552
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23940 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2131 chi ∧
      PredecessorHalfFin13Atom0841 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0849
    PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2131 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4552
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23941 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom2132 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23942 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom2132 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23943 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom2132 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23944 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom2132 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23945 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2132 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2132 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23946 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2132 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0850
    PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2132 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23947 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom2133 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23948 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom2133 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23949 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom2133 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23950 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom2133 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23951 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2133 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom2133 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23952 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2133 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0844 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom0851
    PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom2133 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2760
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23953 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom2134 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23954 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom2134 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23955 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom2134 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23956 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom2134 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23957 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2134 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2134 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23958 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2134 chi ∧
      PredecessorHalfFin13Atom0842 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0852
    PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2134 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4808
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23959 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom2135 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23960 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom2135 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23961 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom2135 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23962 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom2135 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23963 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2135 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2135 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3272
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23965 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom2136 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5320
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23966 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom2136 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5320
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23967 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom2136 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5320
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23968 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom2136 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5320
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23969 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2136 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2136 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5320
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23970 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2136 chi ∧
      PredecessorHalfFin13Atom0843 chi ∧
      PredecessorHalfFin13Atom0845 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2136 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5320
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23971 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom2137 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6344
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23972 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom2137 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6344
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23975 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2137 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0976 PredecessorHalfFin13Atom2137 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6344
  ] at hbad
  tauto

end ErdosSzekeres

end
