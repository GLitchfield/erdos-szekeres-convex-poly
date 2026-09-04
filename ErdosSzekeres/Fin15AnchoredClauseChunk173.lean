module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 173. -/

theorem fin15Anchored_clause22144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom3251 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01362
  ] at hbad
  tauto

theorem fin15Anchored_clause22145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom3251 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01362
  ] at hbad
  tauto

theorem fin15Anchored_clause22146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom3251 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01362
  ] at hbad
  tauto

theorem fin15Anchored_clause22147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom3251 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01362
  ] at hbad
  tauto

theorem fin15Anchored_clause22148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3251 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom3251 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01362
  ] at hbad
  tauto

theorem fin15Anchored_clause22149 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom0953 Fin15AnchoredAtom0966
    Fin15AnchoredAtom1030 Fin15AnchoredAtom1535 Fin15AnchoredAtom3251 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01362
  ] at hbad
  tauto

theorem fin15Anchored_clause22150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom3253 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04434
  ] at hbad
  tauto

theorem fin15Anchored_clause22151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom3253 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04434
  ] at hbad
  tauto

theorem fin15Anchored_clause22152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom3253 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04434
  ] at hbad
  tauto

theorem fin15Anchored_clause22153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3253 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom3253 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04434
  ] at hbad
  tauto

theorem fin15Anchored_clause22154 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3253 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom0955 Fin15AnchoredAtom0968
    Fin15AnchoredAtom1032 Fin15AnchoredAtom1537 Fin15AnchoredAtom3253 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04434
  ] at hbad
  tauto

theorem fin15Anchored_clause22155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom3254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08530
  ] at hbad
  tauto

theorem fin15Anchored_clause22156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom3254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08530
  ] at hbad
  tauto

theorem fin15Anchored_clause22157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom3254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08530
  ] at hbad
  tauto

theorem fin15Anchored_clause22158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom3254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08530
  ] at hbad
  tauto

theorem fin15Anchored_clause22159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3254 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1538 Fin15AnchoredAtom3254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08530
  ] at hbad
  tauto

theorem fin15Anchored_clause22160 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom0956 Fin15AnchoredAtom0969
    Fin15AnchoredAtom1033 Fin15AnchoredAtom1538 Fin15AnchoredAtom3254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08530
  ] at hbad
  tauto

theorem fin15Anchored_clause22161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom3255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16722
  ] at hbad
  tauto

theorem fin15Anchored_clause22162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom3255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16722
  ] at hbad
  tauto

theorem fin15Anchored_clause22163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0970 Fin15AnchoredAtom3255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16722
  ] at hbad
  tauto

theorem fin15Anchored_clause22164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1034 Fin15AnchoredAtom3255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16722
  ] at hbad
  tauto

theorem fin15Anchored_clause22165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3255 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1539 Fin15AnchoredAtom3255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16722
  ] at hbad
  tauto

theorem fin15Anchored_clause22166 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3255 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom0957 Fin15AnchoredAtom0970
    Fin15AnchoredAtom1034 Fin15AnchoredAtom1539 Fin15AnchoredAtom3255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16722
  ] at hbad
  tauto

theorem fin15Anchored_clause22167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom3256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01618
  ] at hbad
  tauto

theorem fin15Anchored_clause22168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom3256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01618
  ] at hbad
  tauto

theorem fin15Anchored_clause22169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom3256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01618
  ] at hbad
  tauto

theorem fin15Anchored_clause22170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom3256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01618
  ] at hbad
  tauto

theorem fin15Anchored_clause22171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom3256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01618
  ] at hbad
  tauto

theorem fin15Anchored_clause22172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom0953 Fin15AnchoredAtom0971
    Fin15AnchoredAtom1035 Fin15AnchoredAtom1540 Fin15AnchoredAtom3256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01618
  ] at hbad
  tauto

theorem fin15Anchored_clause22173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3257 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom3257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02642
  ] at hbad
  tauto

theorem fin15Anchored_clause22174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3257 chi ∧
      ¬Fin15AnchoredAtom1036 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1036 Fin15AnchoredAtom3257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02642
  ] at hbad
  tauto

theorem fin15Anchored_clause22175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom3258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04690
  ] at hbad
  tauto

theorem fin15Anchored_clause22176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom3258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04690
  ] at hbad
  tauto

theorem fin15Anchored_clause22177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom3258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04690
  ] at hbad
  tauto

theorem fin15Anchored_clause22178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom3258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04690
  ] at hbad
  tauto

theorem fin15Anchored_clause22179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom3258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04690
  ] at hbad
  tauto

theorem fin15Anchored_clause22180 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom0955 Fin15AnchoredAtom0973
    Fin15AnchoredAtom1037 Fin15AnchoredAtom1542 Fin15AnchoredAtom3258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04690
  ] at hbad
  tauto

theorem fin15Anchored_clause22181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom3259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08786
  ] at hbad
  tauto

theorem fin15Anchored_clause22182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom3259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08786
  ] at hbad
  tauto

theorem fin15Anchored_clause22183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom3259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08786
  ] at hbad
  tauto

theorem fin15Anchored_clause22184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom3259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08786
  ] at hbad
  tauto

theorem fin15Anchored_clause22185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom3259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08786
  ] at hbad
  tauto

theorem fin15Anchored_clause22186 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom0956 Fin15AnchoredAtom0974
    Fin15AnchoredAtom1038 Fin15AnchoredAtom1543 Fin15AnchoredAtom3259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08786
  ] at hbad
  tauto

theorem fin15Anchored_clause22187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom3260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16978
  ] at hbad
  tauto

theorem fin15Anchored_clause22188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom3260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16978
  ] at hbad
  tauto

theorem fin15Anchored_clause22189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom3260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16978
  ] at hbad
  tauto

theorem fin15Anchored_clause22190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom3260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16978
  ] at hbad
  tauto

theorem fin15Anchored_clause22191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom3260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16978
  ] at hbad
  tauto

theorem fin15Anchored_clause22192 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom0957 Fin15AnchoredAtom0975
    Fin15AnchoredAtom1039 Fin15AnchoredAtom1544 Fin15AnchoredAtom3260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16978
  ] at hbad
  tauto

theorem fin15Anchored_clause22193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom3261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03154
  ] at hbad
  tauto

theorem fin15Anchored_clause22194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom0954 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0954 Fin15AnchoredAtom3261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03154
  ] at hbad
  tauto

theorem fin15Anchored_clause22195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1040 Fin15AnchoredAtom3261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03154
  ] at hbad
  tauto

theorem fin15Anchored_clause22196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3261 chi ∧
      ¬Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1545 Fin15AnchoredAtom3261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03154
  ] at hbad
  tauto

theorem fin15Anchored_clause22197 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3261 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0954 chi ∧
      Fin15AnchoredAtom0976 chi ∧
      Fin15AnchoredAtom1040 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom0954 Fin15AnchoredAtom0976
    Fin15AnchoredAtom1040 Fin15AnchoredAtom1545 Fin15AnchoredAtom3261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03154
  ] at hbad
  tauto

theorem fin15Anchored_clause22198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom3262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05202
  ] at hbad
  tauto

theorem fin15Anchored_clause22199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom3262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05202
  ] at hbad
  tauto

theorem fin15Anchored_clause22200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom3262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05202
  ] at hbad
  tauto

theorem fin15Anchored_clause22201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom3262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05202
  ] at hbad
  tauto

theorem fin15Anchored_clause22202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom3262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05202
  ] at hbad
  tauto

theorem fin15Anchored_clause22203 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom0955 Fin15AnchoredAtom0977
    Fin15AnchoredAtom1041 Fin15AnchoredAtom1546 Fin15AnchoredAtom3262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05202
  ] at hbad
  tauto

theorem fin15Anchored_clause22204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom3263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09298
  ] at hbad
  tauto

theorem fin15Anchored_clause22205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom3263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09298
  ] at hbad
  tauto

theorem fin15Anchored_clause22206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom3263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09298
  ] at hbad
  tauto

theorem fin15Anchored_clause22207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom3263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09298
  ] at hbad
  tauto

theorem fin15Anchored_clause22208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom3263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09298
  ] at hbad
  tauto

theorem fin15Anchored_clause22209 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom0956 Fin15AnchoredAtom0978
    Fin15AnchoredAtom1042 Fin15AnchoredAtom1547 Fin15AnchoredAtom3263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09298
  ] at hbad
  tauto

theorem fin15Anchored_clause22210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom3264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17490
  ] at hbad
  tauto

theorem fin15Anchored_clause22211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom3264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17490
  ] at hbad
  tauto

theorem fin15Anchored_clause22212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom3264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17490
  ] at hbad
  tauto

theorem fin15Anchored_clause22213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom3264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17490
  ] at hbad
  tauto

theorem fin15Anchored_clause22214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom3264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17490
  ] at hbad
  tauto

theorem fin15Anchored_clause22215 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom0957 Fin15AnchoredAtom0979
    Fin15AnchoredAtom1043 Fin15AnchoredAtom1548 Fin15AnchoredAtom3264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17490
  ] at hbad
  tauto

theorem fin15Anchored_clause22216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3265 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom3265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06226
  ] at hbad
  tauto

theorem fin15Anchored_clause22217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3266 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom3266 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10322
  ] at hbad
  tauto

theorem fin15Anchored_clause22218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom3268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12370
  ] at hbad
  tauto

theorem fin15Anchored_clause22219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom3268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12370
  ] at hbad
  tauto

theorem fin15Anchored_clause22220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom3268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12370
  ] at hbad
  tauto

theorem fin15Anchored_clause22221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom3268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12370
  ] at hbad
  tauto

theorem fin15Anchored_clause22222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom3268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12370
  ] at hbad
  tauto

theorem fin15Anchored_clause22223 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom0956 Fin15AnchoredAtom0983
    Fin15AnchoredAtom1047 Fin15AnchoredAtom1552 Fin15AnchoredAtom3268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12370
  ] at hbad
  tauto

theorem fin15Anchored_clause22224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom3269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20562
  ] at hbad
  tauto

theorem fin15Anchored_clause22225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom3269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20562
  ] at hbad
  tauto

theorem fin15Anchored_clause22226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom3269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20562
  ] at hbad
  tauto

theorem fin15Anchored_clause22227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom3269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20562
  ] at hbad
  tauto

theorem fin15Anchored_clause22228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom3269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20562
  ] at hbad
  tauto

theorem fin15Anchored_clause22229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom0957 Fin15AnchoredAtom0984
    Fin15AnchoredAtom1048 Fin15AnchoredAtom1553 Fin15AnchoredAtom3269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20562
  ] at hbad
  tauto

theorem fin15Anchored_clause22230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom3270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24658
  ] at hbad
  tauto

theorem fin15Anchored_clause22231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom3270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24658
  ] at hbad
  tauto

theorem fin15Anchored_clause22232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom3270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24658
  ] at hbad
  tauto

theorem fin15Anchored_clause22233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom3270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24658
  ] at hbad
  tauto

theorem fin15Anchored_clause22234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom3270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24658
  ] at hbad
  tauto

theorem fin15Anchored_clause22235 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom0957 Fin15AnchoredAtom0985
    Fin15AnchoredAtom1049 Fin15AnchoredAtom1554 Fin15AnchoredAtom3270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24658
  ] at hbad
  tauto

theorem fin15Anchored_clause22236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom3271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00914
  ] at hbad
  tauto

theorem fin15Anchored_clause22237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom3271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00914
  ] at hbad
  tauto

theorem fin15Anchored_clause22238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom3271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00914
  ] at hbad
  tauto

theorem fin15Anchored_clause22239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom3271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00914
  ] at hbad
  tauto

theorem fin15Anchored_clause22240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3271 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom3271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00914
  ] at hbad
  tauto

theorem fin15Anchored_clause22241 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3271 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom0959 Fin15AnchoredAtom0965
    Fin15AnchoredAtom1050 Fin15AnchoredAtom1555 Fin15AnchoredAtom3271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00914
  ] at hbad
  tauto

theorem fin15Anchored_clause22242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom3272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01426
  ] at hbad
  tauto

theorem fin15Anchored_clause22243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom3272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01426
  ] at hbad
  tauto

theorem fin15Anchored_clause22244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom3272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01426
  ] at hbad
  tauto

theorem fin15Anchored_clause22245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom3272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01426
  ] at hbad
  tauto

theorem fin15Anchored_clause22246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3272 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom3272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01426
  ] at hbad
  tauto

theorem fin15Anchored_clause22247 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3272 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom0960 Fin15AnchoredAtom0966
    Fin15AnchoredAtom1051 Fin15AnchoredAtom1556 Fin15AnchoredAtom3272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01426
  ] at hbad
  tauto

theorem fin15Anchored_clause22248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom3274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04498
  ] at hbad
  tauto

theorem fin15Anchored_clause22249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom3274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04498
  ] at hbad
  tauto

theorem fin15Anchored_clause22250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0968 Fin15AnchoredAtom3274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04498
  ] at hbad
  tauto

theorem fin15Anchored_clause22251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom3274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04498
  ] at hbad
  tauto

theorem fin15Anchored_clause22252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3274 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom3274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04498
  ] at hbad
  tauto

theorem fin15Anchored_clause22253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3274 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom0962 Fin15AnchoredAtom0968
    Fin15AnchoredAtom1053 Fin15AnchoredAtom1558 Fin15AnchoredAtom3274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04498
  ] at hbad
  tauto

theorem fin15Anchored_clause22254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom3275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08594
  ] at hbad
  tauto

theorem fin15Anchored_clause22255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom3275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08594
  ] at hbad
  tauto

theorem fin15Anchored_clause22256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom3275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08594
  ] at hbad
  tauto

theorem fin15Anchored_clause22257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom3275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08594
  ] at hbad
  tauto

theorem fin15Anchored_clause22258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3275 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom3275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08594
  ] at hbad
  tauto

theorem fin15Anchored_clause22259 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3275 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom0963 Fin15AnchoredAtom0969
    Fin15AnchoredAtom1054 Fin15AnchoredAtom1559 Fin15AnchoredAtom3275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08594
  ] at hbad
  tauto

theorem fin15Anchored_clause22260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom3276 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16786
  ] at hbad
  tauto

theorem fin15Anchored_clause22261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0970 Fin15AnchoredAtom3276 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16786
  ] at hbad
  tauto

theorem fin15Anchored_clause22262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1055 Fin15AnchoredAtom3276 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16786
  ] at hbad
  tauto

theorem fin15Anchored_clause22263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3276 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom3276 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16786
  ] at hbad
  tauto

theorem fin15Anchored_clause22264 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3276 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom0964 Fin15AnchoredAtom0970
    Fin15AnchoredAtom1055 Fin15AnchoredAtom1560 Fin15AnchoredAtom3276 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16786
  ] at hbad
  tauto

theorem fin15Anchored_clause22265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom3277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01682
  ] at hbad
  tauto

theorem fin15Anchored_clause22266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom3277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01682
  ] at hbad
  tauto

theorem fin15Anchored_clause22267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom3277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01682
  ] at hbad
  tauto

theorem fin15Anchored_clause22268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom3277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01682
  ] at hbad
  tauto

theorem fin15Anchored_clause22269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom3277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01682
  ] at hbad
  tauto

theorem fin15Anchored_clause22270 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom0960 Fin15AnchoredAtom0971
    Fin15AnchoredAtom1056 Fin15AnchoredAtom1561 Fin15AnchoredAtom3277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01682
  ] at hbad
  tauto

theorem fin15Anchored_clause22271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3278 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom3278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02706
  ] at hbad
  tauto

end ErdosSzekeres

end
