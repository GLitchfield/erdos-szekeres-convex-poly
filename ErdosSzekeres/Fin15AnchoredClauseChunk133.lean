module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 133. -/

theorem fin15Anchored_clause17024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04237
  ] at hbad
  tauto

theorem fin15Anchored_clause17025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04237
  ] at hbad
  tauto

theorem fin15Anchored_clause17026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom0631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0631 Fin15AnchoredAtom2138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04237
  ] at hbad
  tauto

theorem fin15Anchored_clause17027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom2138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04237
  ] at hbad
  tauto

theorem fin15Anchored_clause17028 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0631 chi ∧
      Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom0542 Fin15AnchoredAtom0576
    Fin15AnchoredAtom0631 Fin15AnchoredAtom1137 Fin15AnchoredAtom2138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04237
  ] at hbad
  tauto

theorem fin15Anchored_clause17029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08333
  ] at hbad
  tauto

theorem fin15Anchored_clause17030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08333
  ] at hbad
  tauto

theorem fin15Anchored_clause17031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08333
  ] at hbad
  tauto

theorem fin15Anchored_clause17032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom0632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0632 Fin15AnchoredAtom2139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08333
  ] at hbad
  tauto

theorem fin15Anchored_clause17033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom2139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08333
  ] at hbad
  tauto

theorem fin15Anchored_clause17034 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0632 chi ∧
      Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom0543 Fin15AnchoredAtom0577
    Fin15AnchoredAtom0632 Fin15AnchoredAtom1138 Fin15AnchoredAtom2139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08333
  ] at hbad
  tauto

theorem fin15Anchored_clause17035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16525
  ] at hbad
  tauto

theorem fin15Anchored_clause17036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom2140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16525
  ] at hbad
  tauto

theorem fin15Anchored_clause17037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16525
  ] at hbad
  tauto

theorem fin15Anchored_clause17038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom0633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0633 Fin15AnchoredAtom2140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16525
  ] at hbad
  tauto

theorem fin15Anchored_clause17039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom2140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16525
  ] at hbad
  tauto

theorem fin15Anchored_clause17040 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0633 chi ∧
      Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom0544 Fin15AnchoredAtom0578
    Fin15AnchoredAtom0633 Fin15AnchoredAtom1139 Fin15AnchoredAtom2140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16525
  ] at hbad
  tauto

theorem fin15Anchored_clause17041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2141 chi ∧
      ¬Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom2141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00781
  ] at hbad
  tauto

theorem fin15Anchored_clause17042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2141 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00781
  ] at hbad
  tauto

theorem fin15Anchored_clause17043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2141 chi ∧
      ¬Fin15AnchoredAtom0579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0579 Fin15AnchoredAtom2141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00781
  ] at hbad
  tauto

theorem fin15Anchored_clause17044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2141 chi ∧
      ¬Fin15AnchoredAtom1140 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1140 Fin15AnchoredAtom2141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00781
  ] at hbad
  tauto

theorem fin15Anchored_clause17045 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom1140 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom0539 Fin15AnchoredAtom0579
    Fin15AnchoredAtom0634 Fin15AnchoredAtom1140 Fin15AnchoredAtom2141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00781
  ] at hbad
  tauto

theorem fin15Anchored_clause17046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom2142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01293
  ] at hbad
  tauto

theorem fin15Anchored_clause17047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01293
  ] at hbad
  tauto

theorem fin15Anchored_clause17048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom0580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0580 Fin15AnchoredAtom2142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01293
  ] at hbad
  tauto

theorem fin15Anchored_clause17049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom2142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01293
  ] at hbad
  tauto

theorem fin15Anchored_clause17050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2142 chi ∧
      ¬Fin15AnchoredAtom1141 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1141 Fin15AnchoredAtom2142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01293
  ] at hbad
  tauto

theorem fin15Anchored_clause17051 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom1141 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom0540 Fin15AnchoredAtom0580
    Fin15AnchoredAtom0635 Fin15AnchoredAtom1141 Fin15AnchoredAtom2142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01293
  ] at hbad
  tauto

theorem fin15Anchored_clause17052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom2144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04365
  ] at hbad
  tauto

theorem fin15Anchored_clause17053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04365
  ] at hbad
  tauto

theorem fin15Anchored_clause17054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom0582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0582 Fin15AnchoredAtom2144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04365
  ] at hbad
  tauto

theorem fin15Anchored_clause17055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom2144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04365
  ] at hbad
  tauto

theorem fin15Anchored_clause17056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2144 chi ∧
      ¬Fin15AnchoredAtom1143 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1143 Fin15AnchoredAtom2144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04365
  ] at hbad
  tauto

theorem fin15Anchored_clause17057 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2144 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom1143 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom0542 Fin15AnchoredAtom0582
    Fin15AnchoredAtom0637 Fin15AnchoredAtom1143 Fin15AnchoredAtom2144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04365
  ] at hbad
  tauto

theorem fin15Anchored_clause17058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2145 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08461
  ] at hbad
  tauto

theorem fin15Anchored_clause17059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2146 chi ∧
      ¬Fin15AnchoredAtom0584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0584 Fin15AnchoredAtom2146 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16653
  ] at hbad
  tauto

theorem fin15Anchored_clause17060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2146 chi ∧
      ¬Fin15AnchoredAtom1145 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1145 Fin15AnchoredAtom2146 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16653
  ] at hbad
  tauto

theorem fin15Anchored_clause17061 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2146 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom1145 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom0544 Fin15AnchoredAtom0584
    Fin15AnchoredAtom0639 Fin15AnchoredAtom1145 Fin15AnchoredAtom2146 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16653
  ] at hbad
  tauto

theorem fin15Anchored_clause17062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01549
  ] at hbad
  tauto

theorem fin15Anchored_clause17063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01549
  ] at hbad
  tauto

theorem fin15Anchored_clause17064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01549
  ] at hbad
  tauto

theorem fin15Anchored_clause17065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01549
  ] at hbad
  tauto

theorem fin15Anchored_clause17066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom2147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01549
  ] at hbad
  tauto

theorem fin15Anchored_clause17067 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom0540 Fin15AnchoredAtom0585
    Fin15AnchoredAtom0640 Fin15AnchoredAtom1146 Fin15AnchoredAtom2147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01549
  ] at hbad
  tauto

theorem fin15Anchored_clause17068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02573
  ] at hbad
  tauto

theorem fin15Anchored_clause17069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2148 chi ∧
      ¬Fin15AnchoredAtom1147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1147 Fin15AnchoredAtom2148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02573
  ] at hbad
  tauto

theorem fin15Anchored_clause17070 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2148 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom1147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom0541 Fin15AnchoredAtom0586
    Fin15AnchoredAtom0641 Fin15AnchoredAtom1147 Fin15AnchoredAtom2148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02573
  ] at hbad
  tauto

theorem fin15Anchored_clause17071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04621
  ] at hbad
  tauto

theorem fin15Anchored_clause17072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04621
  ] at hbad
  tauto

theorem fin15Anchored_clause17073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom2149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04621
  ] at hbad
  tauto

theorem fin15Anchored_clause17074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04621
  ] at hbad
  tauto

theorem fin15Anchored_clause17075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom2149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04621
  ] at hbad
  tauto

theorem fin15Anchored_clause17076 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom0542 Fin15AnchoredAtom0587
    Fin15AnchoredAtom0642 Fin15AnchoredAtom1148 Fin15AnchoredAtom2149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04621
  ] at hbad
  tauto

theorem fin15Anchored_clause17077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08717
  ] at hbad
  tauto

theorem fin15Anchored_clause17078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08717
  ] at hbad
  tauto

theorem fin15Anchored_clause17079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom2150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08717
  ] at hbad
  tauto

theorem fin15Anchored_clause17080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom2150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08717
  ] at hbad
  tauto

theorem fin15Anchored_clause17081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom2150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08717
  ] at hbad
  tauto

theorem fin15Anchored_clause17082 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom0543 Fin15AnchoredAtom0588
    Fin15AnchoredAtom0643 Fin15AnchoredAtom1149 Fin15AnchoredAtom2150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08717
  ] at hbad
  tauto

theorem fin15Anchored_clause17083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16909
  ] at hbad
  tauto

theorem fin15Anchored_clause17084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom2151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16909
  ] at hbad
  tauto

theorem fin15Anchored_clause17085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16909
  ] at hbad
  tauto

theorem fin15Anchored_clause17086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom2151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16909
  ] at hbad
  tauto

theorem fin15Anchored_clause17087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom2151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16909
  ] at hbad
  tauto

theorem fin15Anchored_clause17088 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom0544 Fin15AnchoredAtom0589
    Fin15AnchoredAtom0644 Fin15AnchoredAtom1150 Fin15AnchoredAtom2151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16909
  ] at hbad
  tauto

theorem fin15Anchored_clause17089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03085
  ] at hbad
  tauto

theorem fin15Anchored_clause17090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom0541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom2152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03085
  ] at hbad
  tauto

theorem fin15Anchored_clause17091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom0590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0590 Fin15AnchoredAtom2152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03085
  ] at hbad
  tauto

theorem fin15Anchored_clause17092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom0645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0645 Fin15AnchoredAtom2152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03085
  ] at hbad
  tauto

theorem fin15Anchored_clause17093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2152 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1151 Fin15AnchoredAtom2152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03085
  ] at hbad
  tauto

theorem fin15Anchored_clause17094 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom0541 Fin15AnchoredAtom0590
    Fin15AnchoredAtom0645 Fin15AnchoredAtom1151 Fin15AnchoredAtom2152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03085
  ] at hbad
  tauto

theorem fin15Anchored_clause17095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05133
  ] at hbad
  tauto

theorem fin15Anchored_clause17096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05133
  ] at hbad
  tauto

theorem fin15Anchored_clause17097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom2153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05133
  ] at hbad
  tauto

theorem fin15Anchored_clause17098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05133
  ] at hbad
  tauto

theorem fin15Anchored_clause17099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom2153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05133
  ] at hbad
  tauto

theorem fin15Anchored_clause17100 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom0542 Fin15AnchoredAtom0591
    Fin15AnchoredAtom0646 Fin15AnchoredAtom1152 Fin15AnchoredAtom2153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05133
  ] at hbad
  tauto

theorem fin15Anchored_clause17101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09229
  ] at hbad
  tauto

theorem fin15Anchored_clause17102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09229
  ] at hbad
  tauto

theorem fin15Anchored_clause17103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom2154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09229
  ] at hbad
  tauto

theorem fin15Anchored_clause17104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09229
  ] at hbad
  tauto

theorem fin15Anchored_clause17105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom2154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09229
  ] at hbad
  tauto

theorem fin15Anchored_clause17106 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom0543 Fin15AnchoredAtom0592
    Fin15AnchoredAtom0647 Fin15AnchoredAtom1153 Fin15AnchoredAtom2154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09229
  ] at hbad
  tauto

theorem fin15Anchored_clause17107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17421
  ] at hbad
  tauto

theorem fin15Anchored_clause17108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom2155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17421
  ] at hbad
  tauto

theorem fin15Anchored_clause17109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom2155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17421
  ] at hbad
  tauto

theorem fin15Anchored_clause17110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17421
  ] at hbad
  tauto

theorem fin15Anchored_clause17111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1154 Fin15AnchoredAtom2155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17421
  ] at hbad
  tauto

theorem fin15Anchored_clause17112 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom0544 Fin15AnchoredAtom0593
    Fin15AnchoredAtom0648 Fin15AnchoredAtom1154 Fin15AnchoredAtom2155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17421
  ] at hbad
  tauto

theorem fin15Anchored_clause17113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2156 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06157
  ] at hbad
  tauto

theorem fin15Anchored_clause17114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2156 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom1155 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom0542 Fin15AnchoredAtom0594
    Fin15AnchoredAtom0649 Fin15AnchoredAtom1155 Fin15AnchoredAtom2156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06157
  ] at hbad
  tauto

theorem fin15Anchored_clause17115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom0541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom2157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10253
  ] at hbad
  tauto

theorem fin15Anchored_clause17116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10253
  ] at hbad
  tauto

theorem fin15Anchored_clause17117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom0595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0595 Fin15AnchoredAtom2157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10253
  ] at hbad
  tauto

theorem fin15Anchored_clause17118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2157 chi ∧
      ¬Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1156 Fin15AnchoredAtom2157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10253
  ] at hbad
  tauto

theorem fin15Anchored_clause17119 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2157 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom0543 Fin15AnchoredAtom0595
    Fin15AnchoredAtom0650 Fin15AnchoredAtom1156 Fin15AnchoredAtom2157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10253
  ] at hbad
  tauto

theorem fin15Anchored_clause17120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom0541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom2158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18445
  ] at hbad
  tauto

theorem fin15Anchored_clause17121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom2158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18445
  ] at hbad
  tauto

theorem fin15Anchored_clause17122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom0596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0596 Fin15AnchoredAtom2158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18445
  ] at hbad
  tauto

theorem fin15Anchored_clause17123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom0651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0651 Fin15AnchoredAtom2158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18445
  ] at hbad
  tauto

theorem fin15Anchored_clause17124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2158 chi ∧
      ¬Fin15AnchoredAtom1157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1157 Fin15AnchoredAtom2158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18445
  ] at hbad
  tauto

theorem fin15Anchored_clause17125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2158 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom1157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom0544 Fin15AnchoredAtom0596
    Fin15AnchoredAtom0651 Fin15AnchoredAtom1157 Fin15AnchoredAtom2158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18445
  ] at hbad
  tauto

theorem fin15Anchored_clause17126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12301
  ] at hbad
  tauto

theorem fin15Anchored_clause17127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12301
  ] at hbad
  tauto

theorem fin15Anchored_clause17128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom2159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12301
  ] at hbad
  tauto

theorem fin15Anchored_clause17129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12301
  ] at hbad
  tauto

theorem fin15Anchored_clause17130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom2159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12301
  ] at hbad
  tauto

theorem fin15Anchored_clause17131 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom0543 Fin15AnchoredAtom0597
    Fin15AnchoredAtom0652 Fin15AnchoredAtom1158 Fin15AnchoredAtom2159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12301
  ] at hbad
  tauto

theorem fin15Anchored_clause17132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20493
  ] at hbad
  tauto

theorem fin15Anchored_clause17133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom2160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20493
  ] at hbad
  tauto

theorem fin15Anchored_clause17134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20493
  ] at hbad
  tauto

theorem fin15Anchored_clause17135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20493
  ] at hbad
  tauto

theorem fin15Anchored_clause17136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1159 Fin15AnchoredAtom2160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20493
  ] at hbad
  tauto

theorem fin15Anchored_clause17137 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom0544 Fin15AnchoredAtom0598
    Fin15AnchoredAtom0653 Fin15AnchoredAtom1159 Fin15AnchoredAtom2160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20493
  ] at hbad
  tauto

theorem fin15Anchored_clause17138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24589
  ] at hbad
  tauto

theorem fin15Anchored_clause17139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom2161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24589
  ] at hbad
  tauto

theorem fin15Anchored_clause17140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom2161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24589
  ] at hbad
  tauto

theorem fin15Anchored_clause17141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24589
  ] at hbad
  tauto

theorem fin15Anchored_clause17142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1160 Fin15AnchoredAtom2161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24589
  ] at hbad
  tauto

theorem fin15Anchored_clause17143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom0544 Fin15AnchoredAtom0599
    Fin15AnchoredAtom0654 Fin15AnchoredAtom1160 Fin15AnchoredAtom2161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24589
  ] at hbad
  tauto

theorem fin15Anchored_clause17144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00117
  ] at hbad
  tauto

theorem fin15Anchored_clause17145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom0546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0546 Fin15AnchoredAtom2162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00117
  ] at hbad
  tauto

theorem fin15Anchored_clause17146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom2162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00117
  ] at hbad
  tauto

theorem fin15Anchored_clause17147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00117
  ] at hbad
  tauto

theorem fin15Anchored_clause17148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom2162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00117
  ] at hbad
  tauto

theorem fin15Anchored_clause17149 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom0545 chi ∧
      Fin15AnchoredAtom0546 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom0546 Fin15AnchoredAtom0555
    Fin15AnchoredAtom0655 Fin15AnchoredAtom1161 Fin15AnchoredAtom2162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00117
  ] at hbad
  tauto

theorem fin15Anchored_clause17150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom0545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0545 Fin15AnchoredAtom2163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00181
  ] at hbad
  tauto

theorem fin15Anchored_clause17151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom0547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0547 Fin15AnchoredAtom2163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00181
  ] at hbad
  tauto

end ErdosSzekeres

end
