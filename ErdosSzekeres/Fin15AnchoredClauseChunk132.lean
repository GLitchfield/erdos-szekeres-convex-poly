module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 132. -/

theorem fin15Anchored_clause16896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom0534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom2116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16413
  ] at hbad
  tauto

theorem fin15Anchored_clause16897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom2116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16413
  ] at hbad
  tauto

theorem fin15Anchored_clause16898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom0554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0554 Fin15AnchoredAtom2116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16413
  ] at hbad
  tauto

theorem fin15Anchored_clause16899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom2116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16413
  ] at hbad
  tauto

theorem fin15Anchored_clause16900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom2116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16413
  ] at hbad
  tauto

theorem fin15Anchored_clause16901 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom0534 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0554 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0534 Fin15AnchoredAtom0544 Fin15AnchoredAtom0554
    Fin15AnchoredAtom0609 Fin15AnchoredAtom1115 Fin15AnchoredAtom2116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16413
  ] at hbad
  tauto

theorem fin15Anchored_clause16902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00109
  ] at hbad
  tauto

theorem fin15Anchored_clause16903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00109
  ] at hbad
  tauto

theorem fin15Anchored_clause16904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom0555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0555 Fin15AnchoredAtom2117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00109
  ] at hbad
  tauto

theorem fin15Anchored_clause16905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom2117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00109
  ] at hbad
  tauto

theorem fin15Anchored_clause16906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom2117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00109
  ] at hbad
  tauto

theorem fin15Anchored_clause16907 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0555 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom0536 Fin15AnchoredAtom0555
    Fin15AnchoredAtom0610 Fin15AnchoredAtom1116 Fin15AnchoredAtom2117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00109
  ] at hbad
  tauto

theorem fin15Anchored_clause16908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2118 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00173
  ] at hbad
  tauto

theorem fin15Anchored_clause16909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2118 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00173
  ] at hbad
  tauto

theorem fin15Anchored_clause16910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom0556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0556 Fin15AnchoredAtom2118 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00173
  ] at hbad
  tauto

theorem fin15Anchored_clause16911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom2118 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00173
  ] at hbad
  tauto

theorem fin15Anchored_clause16912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom2118 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00173
  ] at hbad
  tauto

theorem fin15Anchored_clause16913 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0556 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom0537 Fin15AnchoredAtom0556
    Fin15AnchoredAtom0611 Fin15AnchoredAtom1117 Fin15AnchoredAtom2118 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00173
  ] at hbad
  tauto

theorem fin15Anchored_clause16914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00301
  ] at hbad
  tauto

theorem fin15Anchored_clause16915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom2119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00301
  ] at hbad
  tauto

theorem fin15Anchored_clause16916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom0557 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0557 Fin15AnchoredAtom2119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00301
  ] at hbad
  tauto

theorem fin15Anchored_clause16917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom2119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00301
  ] at hbad
  tauto

theorem fin15Anchored_clause16918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2119 chi ∧
      ¬Fin15AnchoredAtom1118 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1118 Fin15AnchoredAtom2119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00301
  ] at hbad
  tauto

theorem fin15Anchored_clause16919 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0557 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom1118 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom0538 Fin15AnchoredAtom0557
    Fin15AnchoredAtom0612 Fin15AnchoredAtom1118 Fin15AnchoredAtom2119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00301
  ] at hbad
  tauto

theorem fin15Anchored_clause16920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00557
  ] at hbad
  tauto

theorem fin15Anchored_clause16921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00557
  ] at hbad
  tauto

theorem fin15Anchored_clause16922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom0558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0558 Fin15AnchoredAtom2120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00557
  ] at hbad
  tauto

theorem fin15Anchored_clause16923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom2120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00557
  ] at hbad
  tauto

theorem fin15Anchored_clause16924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom2120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00557
  ] at hbad
  tauto

theorem fin15Anchored_clause16925 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0558 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom0539 Fin15AnchoredAtom0558
    Fin15AnchoredAtom0613 Fin15AnchoredAtom1119 Fin15AnchoredAtom2120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00557
  ] at hbad
  tauto

theorem fin15Anchored_clause16926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01069
  ] at hbad
  tauto

theorem fin15Anchored_clause16927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01069
  ] at hbad
  tauto

theorem fin15Anchored_clause16928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom0559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0559 Fin15AnchoredAtom2121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01069
  ] at hbad
  tauto

theorem fin15Anchored_clause16929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom2121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01069
  ] at hbad
  tauto

theorem fin15Anchored_clause16930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom2121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01069
  ] at hbad
  tauto

theorem fin15Anchored_clause16931 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0559 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom0540 Fin15AnchoredAtom0559
    Fin15AnchoredAtom0614 Fin15AnchoredAtom1120 Fin15AnchoredAtom2121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01069
  ] at hbad
  tauto

theorem fin15Anchored_clause16932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02093
  ] at hbad
  tauto

theorem fin15Anchored_clause16933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom0541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom2122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02093
  ] at hbad
  tauto

theorem fin15Anchored_clause16934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom0560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0560 Fin15AnchoredAtom2122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02093
  ] at hbad
  tauto

theorem fin15Anchored_clause16935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2122 chi ∧
      ¬Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1121 Fin15AnchoredAtom2122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02093
  ] at hbad
  tauto

theorem fin15Anchored_clause16936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0560 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom0541 Fin15AnchoredAtom0560
    Fin15AnchoredAtom0615 Fin15AnchoredAtom1121 Fin15AnchoredAtom2122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02093
  ] at hbad
  tauto

theorem fin15Anchored_clause16937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04141
  ] at hbad
  tauto

theorem fin15Anchored_clause16938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04141
  ] at hbad
  tauto

theorem fin15Anchored_clause16939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom0561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0561 Fin15AnchoredAtom2123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04141
  ] at hbad
  tauto

theorem fin15Anchored_clause16940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom2123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04141
  ] at hbad
  tauto

theorem fin15Anchored_clause16941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom2123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04141
  ] at hbad
  tauto

theorem fin15Anchored_clause16942 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0561 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom0542 Fin15AnchoredAtom0561
    Fin15AnchoredAtom0616 Fin15AnchoredAtom1122 Fin15AnchoredAtom2123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04141
  ] at hbad
  tauto

theorem fin15Anchored_clause16943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08237
  ] at hbad
  tauto

theorem fin15Anchored_clause16944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08237
  ] at hbad
  tauto

theorem fin15Anchored_clause16945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom0562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0562 Fin15AnchoredAtom2124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08237
  ] at hbad
  tauto

theorem fin15Anchored_clause16946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom2124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08237
  ] at hbad
  tauto

theorem fin15Anchored_clause16947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom2124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08237
  ] at hbad
  tauto

theorem fin15Anchored_clause16948 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0562 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom0543 Fin15AnchoredAtom0562
    Fin15AnchoredAtom0617 Fin15AnchoredAtom1123 Fin15AnchoredAtom2124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08237
  ] at hbad
  tauto

theorem fin15Anchored_clause16949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom0535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom2125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16429
  ] at hbad
  tauto

theorem fin15Anchored_clause16950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom2125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16429
  ] at hbad
  tauto

theorem fin15Anchored_clause16951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom0563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0563 Fin15AnchoredAtom2125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16429
  ] at hbad
  tauto

theorem fin15Anchored_clause16952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom2125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16429
  ] at hbad
  tauto

theorem fin15Anchored_clause16953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1124 Fin15AnchoredAtom2125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16429
  ] at hbad
  tauto

theorem fin15Anchored_clause16954 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom0535 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0563 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0535 Fin15AnchoredAtom0544 Fin15AnchoredAtom0563
    Fin15AnchoredAtom0618 Fin15AnchoredAtom1124 Fin15AnchoredAtom2125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16429
  ] at hbad
  tauto

theorem fin15Anchored_clause16955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2126 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00205
  ] at hbad
  tauto

theorem fin15Anchored_clause16956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2126 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00205
  ] at hbad
  tauto

theorem fin15Anchored_clause16957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom2126 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00205
  ] at hbad
  tauto

theorem fin15Anchored_clause16958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom2126 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00205
  ] at hbad
  tauto

theorem fin15Anchored_clause16959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom2126 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00205
  ] at hbad
  tauto

theorem fin15Anchored_clause16960 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom0537 Fin15AnchoredAtom0564
    Fin15AnchoredAtom0619 Fin15AnchoredAtom1125 Fin15AnchoredAtom2126 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00205
  ] at hbad
  tauto

theorem fin15Anchored_clause16961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00333
  ] at hbad
  tauto

theorem fin15Anchored_clause16962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom2127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00333
  ] at hbad
  tauto

theorem fin15Anchored_clause16963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom0565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0565 Fin15AnchoredAtom2127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00333
  ] at hbad
  tauto

theorem fin15Anchored_clause16964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom2127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00333
  ] at hbad
  tauto

theorem fin15Anchored_clause16965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2127 chi ∧
      ¬Fin15AnchoredAtom1126 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1126 Fin15AnchoredAtom2127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00333
  ] at hbad
  tauto

theorem fin15Anchored_clause16966 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2127 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom1126 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom0538 Fin15AnchoredAtom0565
    Fin15AnchoredAtom0620 Fin15AnchoredAtom1126 Fin15AnchoredAtom2127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00333
  ] at hbad
  tauto

theorem fin15Anchored_clause16967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00589
  ] at hbad
  tauto

theorem fin15Anchored_clause16968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00589
  ] at hbad
  tauto

theorem fin15Anchored_clause16969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00589
  ] at hbad
  tauto

theorem fin15Anchored_clause16970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom2128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00589
  ] at hbad
  tauto

theorem fin15Anchored_clause16971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom2128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00589
  ] at hbad
  tauto

theorem fin15Anchored_clause16972 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom0539 Fin15AnchoredAtom0566
    Fin15AnchoredAtom0621 Fin15AnchoredAtom1127 Fin15AnchoredAtom2128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00589
  ] at hbad
  tauto

theorem fin15Anchored_clause16973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01101
  ] at hbad
  tauto

theorem fin15Anchored_clause16974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01101
  ] at hbad
  tauto

theorem fin15Anchored_clause16975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01101
  ] at hbad
  tauto

theorem fin15Anchored_clause16976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom2129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01101
  ] at hbad
  tauto

theorem fin15Anchored_clause16977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom2129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01101
  ] at hbad
  tauto

theorem fin15Anchored_clause16978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom0540 Fin15AnchoredAtom0567
    Fin15AnchoredAtom0622 Fin15AnchoredAtom1128 Fin15AnchoredAtom2129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01101
  ] at hbad
  tauto

theorem fin15Anchored_clause16979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02125
  ] at hbad
  tauto

theorem fin15Anchored_clause16980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom0541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0541 Fin15AnchoredAtom2130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02125
  ] at hbad
  tauto

theorem fin15Anchored_clause16981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom0568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0568 Fin15AnchoredAtom2130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02125
  ] at hbad
  tauto

theorem fin15Anchored_clause16982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2130 chi ∧
      ¬Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1129 Fin15AnchoredAtom2130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02125
  ] at hbad
  tauto

theorem fin15Anchored_clause16983 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2130 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0623 chi ∧
      Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom0541 Fin15AnchoredAtom0568
    Fin15AnchoredAtom0623 Fin15AnchoredAtom1129 Fin15AnchoredAtom2130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02125
  ] at hbad
  tauto

theorem fin15Anchored_clause16984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04173
  ] at hbad
  tauto

theorem fin15Anchored_clause16985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom0542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0542 Fin15AnchoredAtom2131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04173
  ] at hbad
  tauto

theorem fin15Anchored_clause16986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04173
  ] at hbad
  tauto

theorem fin15Anchored_clause16987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom2131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04173
  ] at hbad
  tauto

theorem fin15Anchored_clause16988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom2131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04173
  ] at hbad
  tauto

theorem fin15Anchored_clause16989 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0542 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom0542 Fin15AnchoredAtom0569
    Fin15AnchoredAtom0624 Fin15AnchoredAtom1130 Fin15AnchoredAtom2131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04173
  ] at hbad
  tauto

theorem fin15Anchored_clause16990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2132 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08269
  ] at hbad
  tauto

theorem fin15Anchored_clause16991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom0543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0543 Fin15AnchoredAtom2132 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08269
  ] at hbad
  tauto

theorem fin15Anchored_clause16992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2132 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08269
  ] at hbad
  tauto

theorem fin15Anchored_clause16993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom0625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0625 Fin15AnchoredAtom2132 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08269
  ] at hbad
  tauto

theorem fin15Anchored_clause16994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom2132 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08269
  ] at hbad
  tauto

theorem fin15Anchored_clause16995 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0543 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0625 chi ∧
      Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom0543 Fin15AnchoredAtom0570
    Fin15AnchoredAtom0625 Fin15AnchoredAtom1131 Fin15AnchoredAtom2132 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08269
  ] at hbad
  tauto

theorem fin15Anchored_clause16996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom0536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom2133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16461
  ] at hbad
  tauto

theorem fin15Anchored_clause16997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom0544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0544 Fin15AnchoredAtom2133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16461
  ] at hbad
  tauto

theorem fin15Anchored_clause16998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom2133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16461
  ] at hbad
  tauto

theorem fin15Anchored_clause16999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom0626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0626 Fin15AnchoredAtom2133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16461
  ] at hbad
  tauto

theorem fin15Anchored_clause17000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom2133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16461
  ] at hbad
  tauto

theorem fin15Anchored_clause17001 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom0536 chi ∧
      Fin15AnchoredAtom0544 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0626 chi ∧
      Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0536 Fin15AnchoredAtom0544 Fin15AnchoredAtom0571
    Fin15AnchoredAtom0626 Fin15AnchoredAtom1132 Fin15AnchoredAtom2133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16461
  ] at hbad
  tauto

theorem fin15Anchored_clause17002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00397
  ] at hbad
  tauto

theorem fin15Anchored_clause17003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom0538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0538 Fin15AnchoredAtom2134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00397
  ] at hbad
  tauto

theorem fin15Anchored_clause17004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom0572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0572 Fin15AnchoredAtom2134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00397
  ] at hbad
  tauto

theorem fin15Anchored_clause17005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom0627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0627 Fin15AnchoredAtom2134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00397
  ] at hbad
  tauto

theorem fin15Anchored_clause17006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2134 chi ∧
      ¬Fin15AnchoredAtom1133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1133 Fin15AnchoredAtom2134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00397
  ] at hbad
  tauto

theorem fin15Anchored_clause17007 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0538 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0627 chi ∧
      Fin15AnchoredAtom1133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom0538 Fin15AnchoredAtom0572
    Fin15AnchoredAtom0627 Fin15AnchoredAtom1133 Fin15AnchoredAtom2134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00397
  ] at hbad
  tauto

theorem fin15Anchored_clause17008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00653
  ] at hbad
  tauto

theorem fin15Anchored_clause17009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom0539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0539 Fin15AnchoredAtom2135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00653
  ] at hbad
  tauto

theorem fin15Anchored_clause17010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00653
  ] at hbad
  tauto

theorem fin15Anchored_clause17011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom0628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0628 Fin15AnchoredAtom2135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00653
  ] at hbad
  tauto

theorem fin15Anchored_clause17012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom2135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00653
  ] at hbad
  tauto

theorem fin15Anchored_clause17013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0539 chi ∧
      Fin15AnchoredAtom0573 chi ∧
      Fin15AnchoredAtom0628 chi ∧
      Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom0539 Fin15AnchoredAtom0573
    Fin15AnchoredAtom0628 Fin15AnchoredAtom1134 Fin15AnchoredAtom2135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00653
  ] at hbad
  tauto

theorem fin15Anchored_clause17014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01165
  ] at hbad
  tauto

theorem fin15Anchored_clause17015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom0540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0540 Fin15AnchoredAtom2136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01165
  ] at hbad
  tauto

theorem fin15Anchored_clause17016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom2136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01165
  ] at hbad
  tauto

theorem fin15Anchored_clause17017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom0629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0629 Fin15AnchoredAtom2136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01165
  ] at hbad
  tauto

theorem fin15Anchored_clause17018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom2136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01165
  ] at hbad
  tauto

theorem fin15Anchored_clause17019 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0540 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0629 chi ∧
      Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom0540 Fin15AnchoredAtom0574
    Fin15AnchoredAtom0629 Fin15AnchoredAtom1135 Fin15AnchoredAtom2136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01165
  ] at hbad
  tauto

theorem fin15Anchored_clause17020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2137 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2137 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02189
  ] at hbad
  tauto

theorem fin15Anchored_clause17021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2137 chi ∧
      ¬Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1136 Fin15AnchoredAtom2137 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02189
  ] at hbad
  tauto

theorem fin15Anchored_clause17022 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom0537 chi ∧
      Fin15AnchoredAtom0541 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0630 chi ∧
      Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom0541 Fin15AnchoredAtom0575
    Fin15AnchoredAtom0630 Fin15AnchoredAtom1136 Fin15AnchoredAtom2137 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02189
  ] at hbad
  tauto

theorem fin15Anchored_clause17023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom0537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0537 Fin15AnchoredAtom2138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04237
  ] at hbad
  tauto

end ErdosSzekeres

end
