module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 085. -/

theorem predecessorHalfFin13_clause24127 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom2163 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0496
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24128 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom2163 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0496
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24129 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom2163 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0496
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24130 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom2163 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0496
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24131 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2163 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom2163 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0496
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24132 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2163 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0882
    PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom2163 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0496
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24133 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom2164 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24134 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom2164 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24135 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom2164 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24136 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom2164 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24137 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2164 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom2164 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24138 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2164 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0883
    PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom2164 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0752
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24139 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom2165 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24140 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom2165 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24141 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom2165 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24142 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom2165 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24143 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2165 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom2165 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24144 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2165 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0884
    PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom2165 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1264
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24145 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom2166 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24146 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom2166 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24147 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom2166 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24148 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom2166 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24149 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2166 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0935 PredecessorHalfFin13Atom2166 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2288
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24151 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom2167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24152 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom2167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24153 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom2167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24154 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom2167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24155 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2167 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom2167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24156 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2167 chi ∧
      PredecessorHalfFin13Atom0876 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0876 PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom0886
    PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom2167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4336
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24157 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom2168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0880
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24158 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom2168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0880
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24159 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom2168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0880
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24160 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom2168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0880
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24161 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2168 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom2168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0880
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24162 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2168 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0887
    PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom2168 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0880
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24163 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom2169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24164 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom2169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24165 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom2169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24166 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom2169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24167 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2169 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom2169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24168 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2169 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0888
    PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom2169 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1392
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24169 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom2170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24170 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom2170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24171 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom2170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24172 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom2170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24173 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2170 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom2170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24174 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2170 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom0889
    PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom0939 PredecessorHalfFin13Atom2170 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2416
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24175 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0877 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom2171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24176 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom2171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24177 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom2171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24178 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom2171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24179 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2171 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom2171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24180 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2171 chi ∧
      PredecessorHalfFin13Atom0877 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0877 PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom2171 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4464
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24181 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom2172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24182 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom2172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24183 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom2172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24184 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom2172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24185 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2172 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom2172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24186 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2172 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0891
    PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom2172 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1648
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24187 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom2173 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24188 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom2173 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24189 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom2173 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24190 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom2173 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24191 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2173 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0942 PredecessorHalfFin13Atom2173 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2672
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24193 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0878 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom2174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24194 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom2174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24195 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom2174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24196 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom2174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24197 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2174 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom2174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24198 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2174 chi ∧
      PredecessorHalfFin13Atom0878 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0878 PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom0893
    PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom2174 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4720
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24199 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom2175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3184
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24200 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom2175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3184
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24201 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom2175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3184
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24202 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom2175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3184
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24203 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2175 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom2175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3184
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24204 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2175 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0880 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom0894
    PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom0944 PredecessorHalfFin13Atom2175 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3184
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24205 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0879 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom2176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24206 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom2176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24207 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom2176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24208 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom2176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24209 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2176 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom2176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24210 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2176 chi ∧
      PredecessorHalfFin13Atom0879 chi ∧
      PredecessorHalfFin13Atom0881 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0879 PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom2176 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5232
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24211 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0880 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0880 PredecessorHalfFin13Atom2177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24212 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0881 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0881 PredecessorHalfFin13Atom2177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24213 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0896 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0896 PredecessorHalfFin13Atom2177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24214 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0911 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0911 PredecessorHalfFin13Atom2177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24215 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2177 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0946 PredecessorHalfFin13Atom2177 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6256
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24217 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom2178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24218 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom2178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24219 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom2178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24220 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom2178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24221 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2178 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom2178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24222 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2178 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0887
    PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom2178 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0944
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24223 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom2179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24224 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom2179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24225 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom2179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24226 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom2179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24227 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2179 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom2179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24228 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2179 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0888
    PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom2179 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1456
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24229 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom2180 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24230 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom2180 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24231 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom2180 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24232 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom2180 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24233 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2180 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom2180 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24234 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2180 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom0889
    PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0949 PredecessorHalfFin13Atom2180 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2480
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24235 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0882 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom2181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24236 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom2181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24237 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom2181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24238 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom2181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24239 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2181 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom2181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24240 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2181 chi ∧
      PredecessorHalfFin13Atom0882 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0882 PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom0890
    PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom2181 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4528
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24241 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom2182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24242 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom2182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24243 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom2182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24244 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom2182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24245 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2182 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom2182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24246 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2182 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0891
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom2182 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1712
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24247 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom2183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24248 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom2183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24249 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom2183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24250 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom2183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24251 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2183 chi ∧
      ¬PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom2183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24252 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2183 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0885 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0952 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom0892
    PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0952 PredecessorHalfFin13Atom2183 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2736
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24253 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0883 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom2184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24254 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom2184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24255 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom2184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24256 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom2184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24257 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2184 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom2184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4784
  ] at hbad
  tauto

end ErdosSzekeres

end
