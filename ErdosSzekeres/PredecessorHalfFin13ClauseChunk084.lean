module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 084. -/

theorem predecessorHalfFin13_clause23977 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom2138 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23978 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom2138 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23979 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom2138 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23980 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom2138 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23981 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2138 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2138 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23982 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2138 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0850
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom2138 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23983 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom2139 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23984 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom2139 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23985 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom2139 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23986 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom2139 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23987 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2139 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2139 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23988 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2139 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0851 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom0851
    PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0978 PredecessorHalfFin13Atom2139 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2888
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23989 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom2140 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23990 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom2140 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23991 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom2140 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23992 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom2140 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23993 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2140 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2140 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23994 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2140 chi ∧
      PredecessorHalfFin13Atom0846 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0852
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom2140 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4936
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23995 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom2141 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23996 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom2141 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23997 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom2141 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23998 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom2141 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause23999 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2141 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2141 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24000 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2141 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0848 chi ∧
      PredecessorHalfFin13Atom0853 chi ∧
      PredecessorHalfFin13Atom0869 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom0853
    PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom0980 PredecessorHalfFin13Atom2141 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3400
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24001 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom2142 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24002 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom2142 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24003 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom2142 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24004 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom2142 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24005 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2142 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2142 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24006 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2142 chi ∧
      PredecessorHalfFin13Atom0847 chi ∧
      PredecessorHalfFin13Atom0849 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0847 PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom2142 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24007 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0848 PredecessorHalfFin13Atom2143 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24008 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0849 PredecessorHalfFin13Atom2143 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24009 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0855 PredecessorHalfFin13Atom2143 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24011 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2143 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0982 PredecessorHalfFin13Atom2143 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6472
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24013 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom2144 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24014 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom2144 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24015 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom2144 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24016 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom2144 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24017 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2144 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0983 PredecessorHalfFin13Atom2144 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3656
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24019 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom2145 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24020 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom2145 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24021 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom2145 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24022 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom2145 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24023 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2145 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2145 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24024 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2145 chi ∧
      PredecessorHalfFin13Atom0850 chi ∧
      PredecessorHalfFin13Atom0852 chi ∧
      PredecessorHalfFin13Atom0854 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0850 PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom0854
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom2145 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24025 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0851 PredecessorHalfFin13Atom2146 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24026 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0852 PredecessorHalfFin13Atom2146 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24028 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0874 PredecessorHalfFin13Atom2146 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24029 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2146 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0985 PredecessorHalfFin13Atom2146 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6728
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24031 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0853 PredecessorHalfFin13Atom2147 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24032 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0854 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0854 PredecessorHalfFin13Atom2147 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24033 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0855 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0855 PredecessorHalfFin13Atom2147 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24034 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom2147 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24035 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2147 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0986 PredecessorHalfFin13Atom2147 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7240
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24037 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom2148 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24038 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom2148 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24039 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom2148 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24040 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom2148 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24041 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2148 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2148 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24042 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2148 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0860
    PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom2148 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1928
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24043 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom2149 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24044 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom2149 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24045 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom2149 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24046 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom2149 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24047 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2149 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2149 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24048 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2149 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0858 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0867 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom0861
    PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom0988 PredecessorHalfFin13Atom2149 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2952
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24049 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0856 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom2150 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5000
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24050 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom2150 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5000
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24051 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom2150 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5000
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24052 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom2150 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5000
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24053 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2150 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2150 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5000
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24054 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2150 chi ∧
      PredecessorHalfFin13Atom0856 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0856 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0862
    PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom2150 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5000
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24055 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom2151 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24056 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom2151 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24057 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom2151 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24058 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom2151 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24059 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2151 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0990 PredecessorHalfFin13Atom2151 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24061 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0857 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom2152 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24062 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom2152 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24063 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom2152 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24064 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom2152 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24065 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2152 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2152 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24066 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2152 chi ∧
      PredecessorHalfFin13Atom0857 chi ∧
      PredecessorHalfFin13Atom0859 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0857 PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom0864
    PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom2152 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24067 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom0858 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0858 PredecessorHalfFin13Atom2153 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6536
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24068 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom0859 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0859 PredecessorHalfFin13Atom2153 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6536
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24071 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2153 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0992 PredecessorHalfFin13Atom2153 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6536
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24073 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom2154 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24074 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom2154 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24075 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0863 PredecessorHalfFin13Atom2154 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24076 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom2154 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24077 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2154 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2154 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24078 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2154 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0861 chi ∧
      PredecessorHalfFin13Atom0863 chi ∧
      PredecessorHalfFin13Atom0872 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0861 PredecessorHalfFin13Atom0863
    PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom0993 PredecessorHalfFin13Atom2154 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24079 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0860 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom2155 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24080 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom2155 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24081 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom2155 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24082 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom2155 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24083 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2155 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2155 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24084 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2155 chi ∧
      PredecessorHalfFin13Atom0860 chi ∧
      PredecessorHalfFin13Atom0862 chi ∧
      PredecessorHalfFin13Atom0864 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0860 PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom0864
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom2155 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24086 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0862 PredecessorHalfFin13Atom2156 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24087 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0865 PredecessorHalfFin13Atom2156 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24088 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0874 PredecessorHalfFin13Atom2156 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24089 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2156 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0995 PredecessorHalfFin13Atom2156 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6792
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24092 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0864 PredecessorHalfFin13Atom2157 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7304
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24093 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0865 PredecessorHalfFin13Atom2157 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7304
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24094 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom2157 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7304
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24095 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2157 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0996 PredecessorHalfFin13Atom2157 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7304
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24097 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom2158 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24098 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom2158 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24099 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom2158 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24100 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom2158 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24101 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2158 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0997 PredecessorHalfFin13Atom2158 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3848
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24103 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom2159 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24104 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom2159 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24105 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom2159 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24106 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom2159 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24107 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2159 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2159 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24108 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2159 chi ∧
      PredecessorHalfFin13Atom0866 chi ∧
      PredecessorHalfFin13Atom0868 chi ∧
      PredecessorHalfFin13Atom0870 chi ∧
      PredecessorHalfFin13Atom0873 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0866 PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom0870
    PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom2159 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5896
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24109 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0867 PredecessorHalfFin13Atom2160 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24110 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0868 PredecessorHalfFin13Atom2160 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24113 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2160 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0999 PredecessorHalfFin13Atom2160 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6920
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24115 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0869 PredecessorHalfFin13Atom2161 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24116 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0870 PredecessorHalfFin13Atom2161 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24118 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom2161 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24119 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2161 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom1000 PredecessorHalfFin13Atom2161 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7432
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24121 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0872 PredecessorHalfFin13Atom2162 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7688
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24122 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0873 PredecessorHalfFin13Atom2162 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7688
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24123 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0874 PredecessorHalfFin13Atom2162 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7688
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24124 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2162 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0875 PredecessorHalfFin13Atom2162 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7688
  ] at hbad
  tauto

end ErdosSzekeres

end
