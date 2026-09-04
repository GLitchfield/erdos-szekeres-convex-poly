module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 165. -/

theorem fin15Anchored_clause21120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0875 Fin15AnchoredAtom3030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20998
  ] at hbad
  tauto

theorem fin15Anchored_clause21121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0884 Fin15AnchoredAtom3030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20998
  ] at hbad
  tauto

theorem fin15Anchored_clause21122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20998
  ] at hbad
  tauto

theorem fin15Anchored_clause21123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom3030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20998
  ] at hbad
  tauto

theorem fin15Anchored_clause21124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3030 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom0875 Fin15AnchoredAtom0884
    Fin15AnchoredAtom1094 Fin15AnchoredAtom1314 Fin15AnchoredAtom3030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20998
  ] at hbad
  tauto

theorem fin15Anchored_clause21125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom3031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25094
  ] at hbad
  tauto

theorem fin15Anchored_clause21126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0875 Fin15AnchoredAtom3031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25094
  ] at hbad
  tauto

theorem fin15Anchored_clause21127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0885 Fin15AnchoredAtom3031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25094
  ] at hbad
  tauto

theorem fin15Anchored_clause21128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom3031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25094
  ] at hbad
  tauto

theorem fin15Anchored_clause21129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1315 Fin15AnchoredAtom3031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25094
  ] at hbad
  tauto

theorem fin15Anchored_clause21130 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3031 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom0875 Fin15AnchoredAtom0885
    Fin15AnchoredAtom1095 Fin15AnchoredAtom1315 Fin15AnchoredAtom3031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25094
  ] at hbad
  tauto

theorem fin15Anchored_clause21131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3032 chi ∧
      ¬Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1096 Fin15AnchoredAtom3032 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07174
  ] at hbad
  tauto

theorem fin15Anchored_clause21132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3032 chi ∧
      ¬Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1316 Fin15AnchoredAtom3032 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07174
  ] at hbad
  tauto

theorem fin15Anchored_clause21133 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3032 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom1096 chi ∧
      Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0876 Fin15AnchoredAtom0877 Fin15AnchoredAtom0880
    Fin15AnchoredAtom1096 Fin15AnchoredAtom1316 Fin15AnchoredAtom3032 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07174
  ] at hbad
  tauto

theorem fin15Anchored_clause21134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom3035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13318
  ] at hbad
  tauto

theorem fin15Anchored_clause21135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom3035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13318
  ] at hbad
  tauto

theorem fin15Anchored_clause21136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom3035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13318
  ] at hbad
  tauto

theorem fin15Anchored_clause21137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13318
  ] at hbad
  tauto

theorem fin15Anchored_clause21138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom3035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13318
  ] at hbad
  tauto

theorem fin15Anchored_clause21139 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3035 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom0878 Fin15AnchoredAtom0883
    Fin15AnchoredAtom1099 Fin15AnchoredAtom1319 Fin15AnchoredAtom3035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13318
  ] at hbad
  tauto

theorem fin15Anchored_clause21140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom3036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21510
  ] at hbad
  tauto

theorem fin15Anchored_clause21141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0879 Fin15AnchoredAtom3036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21510
  ] at hbad
  tauto

theorem fin15Anchored_clause21142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0884 Fin15AnchoredAtom3036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21510
  ] at hbad
  tauto

theorem fin15Anchored_clause21143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21510
  ] at hbad
  tauto

theorem fin15Anchored_clause21144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom3036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21510
  ] at hbad
  tauto

theorem fin15Anchored_clause21145 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3036 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom0879 Fin15AnchoredAtom0884
    Fin15AnchoredAtom1100 Fin15AnchoredAtom1320 Fin15AnchoredAtom3036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21510
  ] at hbad
  tauto

theorem fin15Anchored_clause21146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom3037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25606
  ] at hbad
  tauto

theorem fin15Anchored_clause21147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0879 Fin15AnchoredAtom3037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25606
  ] at hbad
  tauto

theorem fin15Anchored_clause21148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0885 Fin15AnchoredAtom3037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25606
  ] at hbad
  tauto

theorem fin15Anchored_clause21149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25606
  ] at hbad
  tauto

theorem fin15Anchored_clause21150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom3037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25606
  ] at hbad
  tauto

theorem fin15Anchored_clause21151 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3037 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom0879 Fin15AnchoredAtom0885
    Fin15AnchoredAtom1101 Fin15AnchoredAtom1321 Fin15AnchoredAtom3037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25606
  ] at hbad
  tauto

theorem fin15Anchored_clause21152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3038 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom0881 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom1102 chi ∧
      Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0880 Fin15AnchoredAtom0881 Fin15AnchoredAtom0883
    Fin15AnchoredAtom1102 Fin15AnchoredAtom1322 Fin15AnchoredAtom3038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14342
  ] at hbad
  tauto

theorem fin15Anchored_clause21153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom3041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28678
  ] at hbad
  tauto

theorem fin15Anchored_clause21154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0884 Fin15AnchoredAtom3041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28678
  ] at hbad
  tauto

theorem fin15Anchored_clause21155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0885 Fin15AnchoredAtom3041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28678
  ] at hbad
  tauto

theorem fin15Anchored_clause21156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28678
  ] at hbad
  tauto

theorem fin15Anchored_clause21157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom3041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28678
  ] at hbad
  tauto

theorem fin15Anchored_clause21158 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3041 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom0884 Fin15AnchoredAtom0885
    Fin15AnchoredAtom1105 Fin15AnchoredAtom1325 Fin15AnchoredAtom3041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28678
  ] at hbad
  tauto

theorem fin15Anchored_clause21159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom3042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00122
  ] at hbad
  tauto

theorem fin15Anchored_clause21160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom3042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00122
  ] at hbad
  tauto

theorem fin15Anchored_clause21161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom3042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00122
  ] at hbad
  tauto

theorem fin15Anchored_clause21162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom3042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00122
  ] at hbad
  tauto

theorem fin15Anchored_clause21163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom3042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00122
  ] at hbad
  tauto

theorem fin15Anchored_clause21164 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3042 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom0887 Fin15AnchoredAtom0896
    Fin15AnchoredAtom0941 Fin15AnchoredAtom1326 Fin15AnchoredAtom3042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00122
  ] at hbad
  tauto

theorem fin15Anchored_clause21165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom3043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00186
  ] at hbad
  tauto

theorem fin15Anchored_clause21166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom3043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00186
  ] at hbad
  tauto

theorem fin15Anchored_clause21167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom3043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00186
  ] at hbad
  tauto

theorem fin15Anchored_clause21168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom3043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00186
  ] at hbad
  tauto

theorem fin15Anchored_clause21169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom3043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00186
  ] at hbad
  tauto

theorem fin15Anchored_clause21170 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3043 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom0888 Fin15AnchoredAtom0897
    Fin15AnchoredAtom0942 Fin15AnchoredAtom1327 Fin15AnchoredAtom3043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00186
  ] at hbad
  tauto

theorem fin15Anchored_clause21171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom3044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00314
  ] at hbad
  tauto

theorem fin15Anchored_clause21172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom3044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00314
  ] at hbad
  tauto

theorem fin15Anchored_clause21173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom3044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00314
  ] at hbad
  tauto

theorem fin15Anchored_clause21174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom3044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00314
  ] at hbad
  tauto

theorem fin15Anchored_clause21175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3044 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom3044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00314
  ] at hbad
  tauto

theorem fin15Anchored_clause21176 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3044 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom0889 Fin15AnchoredAtom0898
    Fin15AnchoredAtom0943 Fin15AnchoredAtom1328 Fin15AnchoredAtom3044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00314
  ] at hbad
  tauto

theorem fin15Anchored_clause21177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom3045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00570
  ] at hbad
  tauto

theorem fin15Anchored_clause21178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom3045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00570
  ] at hbad
  tauto

theorem fin15Anchored_clause21179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom3045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00570
  ] at hbad
  tauto

theorem fin15Anchored_clause21180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom3045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00570
  ] at hbad
  tauto

theorem fin15Anchored_clause21181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom3045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00570
  ] at hbad
  tauto

theorem fin15Anchored_clause21182 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3045 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom0890 Fin15AnchoredAtom0899
    Fin15AnchoredAtom0944 Fin15AnchoredAtom1329 Fin15AnchoredAtom3045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00570
  ] at hbad
  tauto

theorem fin15Anchored_clause21183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom3046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01082
  ] at hbad
  tauto

theorem fin15Anchored_clause21184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom3046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01082
  ] at hbad
  tauto

theorem fin15Anchored_clause21185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom3046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01082
  ] at hbad
  tauto

theorem fin15Anchored_clause21186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom3046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01082
  ] at hbad
  tauto

theorem fin15Anchored_clause21187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom3046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01082
  ] at hbad
  tauto

theorem fin15Anchored_clause21188 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom0891 Fin15AnchoredAtom0900
    Fin15AnchoredAtom0945 Fin15AnchoredAtom1330 Fin15AnchoredAtom3046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01082
  ] at hbad
  tauto

theorem fin15Anchored_clause21189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3047 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom3047 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02106
  ] at hbad
  tauto

theorem fin15Anchored_clause21190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom3048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04154
  ] at hbad
  tauto

theorem fin15Anchored_clause21191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom3048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04154
  ] at hbad
  tauto

theorem fin15Anchored_clause21192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom3048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04154
  ] at hbad
  tauto

theorem fin15Anchored_clause21193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom3048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04154
  ] at hbad
  tauto

theorem fin15Anchored_clause21194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom3048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04154
  ] at hbad
  tauto

theorem fin15Anchored_clause21195 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom0893 Fin15AnchoredAtom0902
    Fin15AnchoredAtom0947 Fin15AnchoredAtom1332 Fin15AnchoredAtom3048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04154
  ] at hbad
  tauto

theorem fin15Anchored_clause21196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom3049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08250
  ] at hbad
  tauto

theorem fin15Anchored_clause21197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom3049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08250
  ] at hbad
  tauto

theorem fin15Anchored_clause21198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom3049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08250
  ] at hbad
  tauto

theorem fin15Anchored_clause21199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom3049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08250
  ] at hbad
  tauto

theorem fin15Anchored_clause21200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom3049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08250
  ] at hbad
  tauto

theorem fin15Anchored_clause21201 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom0894 Fin15AnchoredAtom0903
    Fin15AnchoredAtom0948 Fin15AnchoredAtom1333 Fin15AnchoredAtom3049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08250
  ] at hbad
  tauto

theorem fin15Anchored_clause21202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom3050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16442
  ] at hbad
  tauto

theorem fin15Anchored_clause21203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom3050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16442
  ] at hbad
  tauto

theorem fin15Anchored_clause21204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom3050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16442
  ] at hbad
  tauto

theorem fin15Anchored_clause21205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom3050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16442
  ] at hbad
  tauto

theorem fin15Anchored_clause21206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom3050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16442
  ] at hbad
  tauto

theorem fin15Anchored_clause21207 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom0886 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom0895 Fin15AnchoredAtom0904
    Fin15AnchoredAtom0949 Fin15AnchoredAtom1334 Fin15AnchoredAtom3050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16442
  ] at hbad
  tauto

theorem fin15Anchored_clause21208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom3051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00218
  ] at hbad
  tauto

theorem fin15Anchored_clause21209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom3051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00218
  ] at hbad
  tauto

theorem fin15Anchored_clause21210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom3051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00218
  ] at hbad
  tauto

theorem fin15Anchored_clause21211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom3051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00218
  ] at hbad
  tauto

theorem fin15Anchored_clause21212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom3051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00218
  ] at hbad
  tauto

theorem fin15Anchored_clause21213 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0888 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom0888 Fin15AnchoredAtom0905
    Fin15AnchoredAtom0950 Fin15AnchoredAtom1335 Fin15AnchoredAtom3051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00218
  ] at hbad
  tauto

theorem fin15Anchored_clause21214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom3052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00346
  ] at hbad
  tauto

theorem fin15Anchored_clause21215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom3052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00346
  ] at hbad
  tauto

theorem fin15Anchored_clause21216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom3052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00346
  ] at hbad
  tauto

theorem fin15Anchored_clause21217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom3052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00346
  ] at hbad
  tauto

theorem fin15Anchored_clause21218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3052 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom3052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00346
  ] at hbad
  tauto

theorem fin15Anchored_clause21219 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0889 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom0889 Fin15AnchoredAtom0906
    Fin15AnchoredAtom0951 Fin15AnchoredAtom1336 Fin15AnchoredAtom3052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00346
  ] at hbad
  tauto

theorem fin15Anchored_clause21220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom3053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00602
  ] at hbad
  tauto

theorem fin15Anchored_clause21221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom3053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00602
  ] at hbad
  tauto

theorem fin15Anchored_clause21222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom3053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00602
  ] at hbad
  tauto

theorem fin15Anchored_clause21223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom3053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00602
  ] at hbad
  tauto

theorem fin15Anchored_clause21224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom3053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00602
  ] at hbad
  tauto

theorem fin15Anchored_clause21225 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0890 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom0890 Fin15AnchoredAtom0907
    Fin15AnchoredAtom0952 Fin15AnchoredAtom1337 Fin15AnchoredAtom3053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00602
  ] at hbad
  tauto

theorem fin15Anchored_clause21226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom3054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01114
  ] at hbad
  tauto

theorem fin15Anchored_clause21227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom3054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01114
  ] at hbad
  tauto

theorem fin15Anchored_clause21228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom3054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01114
  ] at hbad
  tauto

theorem fin15Anchored_clause21229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom3054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01114
  ] at hbad
  tauto

theorem fin15Anchored_clause21230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom3054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01114
  ] at hbad
  tauto

theorem fin15Anchored_clause21231 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0891 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom0891 Fin15AnchoredAtom0908
    Fin15AnchoredAtom0953 Fin15AnchoredAtom1338 Fin15AnchoredAtom3054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01114
  ] at hbad
  tauto

theorem fin15Anchored_clause21232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3055 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom3055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02138
  ] at hbad
  tauto

theorem fin15Anchored_clause21233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom3056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04186
  ] at hbad
  tauto

theorem fin15Anchored_clause21234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom3056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04186
  ] at hbad
  tauto

theorem fin15Anchored_clause21235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom3056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04186
  ] at hbad
  tauto

theorem fin15Anchored_clause21236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom3056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04186
  ] at hbad
  tauto

theorem fin15Anchored_clause21237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom3056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04186
  ] at hbad
  tauto

theorem fin15Anchored_clause21238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom0893 Fin15AnchoredAtom0910
    Fin15AnchoredAtom0955 Fin15AnchoredAtom1340 Fin15AnchoredAtom3056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04186
  ] at hbad
  tauto

theorem fin15Anchored_clause21239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom3057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08282
  ] at hbad
  tauto

theorem fin15Anchored_clause21240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom3057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08282
  ] at hbad
  tauto

theorem fin15Anchored_clause21241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom3057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08282
  ] at hbad
  tauto

theorem fin15Anchored_clause21242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom3057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08282
  ] at hbad
  tauto

theorem fin15Anchored_clause21243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom3057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08282
  ] at hbad
  tauto

theorem fin15Anchored_clause21244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom0887 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom0894 Fin15AnchoredAtom0911
    Fin15AnchoredAtom0956 Fin15AnchoredAtom1341 Fin15AnchoredAtom3057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08282
  ] at hbad
  tauto

theorem fin15Anchored_clause21245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom3058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16474
  ] at hbad
  tauto

theorem fin15Anchored_clause21246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom3058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16474
  ] at hbad
  tauto

theorem fin15Anchored_clause21247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom3058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16474
  ] at hbad
  tauto

end ErdosSzekeres

end
