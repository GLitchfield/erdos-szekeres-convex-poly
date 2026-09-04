module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 180. -/

theorem fin15Anchored_clause23040 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom1042 Fin15AnchoredAtom1047
    Fin15AnchoredAtom1099 Fin15AnchoredAtom1744 Fin15AnchoredAtom3460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13378
  ] at hbad
  tauto

theorem fin15Anchored_clause23041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom3461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21570
  ] at hbad
  tauto

theorem fin15Anchored_clause23042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom3461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21570
  ] at hbad
  tauto

theorem fin15Anchored_clause23043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom3461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21570
  ] at hbad
  tauto

theorem fin15Anchored_clause23044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21570
  ] at hbad
  tauto

theorem fin15Anchored_clause23045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3461 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom3461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21570
  ] at hbad
  tauto

theorem fin15Anchored_clause23046 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom1043 Fin15AnchoredAtom1048
    Fin15AnchoredAtom1100 Fin15AnchoredAtom1745 Fin15AnchoredAtom3461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21570
  ] at hbad
  tauto

theorem fin15Anchored_clause23047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom3462 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25666
  ] at hbad
  tauto

theorem fin15Anchored_clause23048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom3462 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25666
  ] at hbad
  tauto

theorem fin15Anchored_clause23049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom3462 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25666
  ] at hbad
  tauto

theorem fin15Anchored_clause23050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3462 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25666
  ] at hbad
  tauto

theorem fin15Anchored_clause23051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3462 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom3462 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25666
  ] at hbad
  tauto

theorem fin15Anchored_clause23052 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom1043 Fin15AnchoredAtom1049
    Fin15AnchoredAtom1101 Fin15AnchoredAtom1746 Fin15AnchoredAtom3462 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25666
  ] at hbad
  tauto

theorem fin15Anchored_clause23053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3463 chi ∧
      ¬Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1044 Fin15AnchoredAtom3463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14402
  ] at hbad
  tauto

theorem fin15Anchored_clause23054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3463 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom3463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14402
  ] at hbad
  tauto

theorem fin15Anchored_clause23055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3463 chi ∧
      ¬Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1747 Fin15AnchoredAtom3463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14402
  ] at hbad
  tauto

theorem fin15Anchored_clause23056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3464 chi ∧
      ¬Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1044 Fin15AnchoredAtom3464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22594
  ] at hbad
  tauto

theorem fin15Anchored_clause23057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3464 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom3464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22594
  ] at hbad
  tauto

theorem fin15Anchored_clause23058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom3466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28738
  ] at hbad
  tauto

theorem fin15Anchored_clause23059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom3466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28738
  ] at hbad
  tauto

theorem fin15Anchored_clause23060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom3466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28738
  ] at hbad
  tauto

theorem fin15Anchored_clause23061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28738
  ] at hbad
  tauto

theorem fin15Anchored_clause23062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3466 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom3466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28738
  ] at hbad
  tauto

theorem fin15Anchored_clause23063 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom1048 Fin15AnchoredAtom1049
    Fin15AnchoredAtom1105 Fin15AnchoredAtom1750 Fin15AnchoredAtom3466 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28738
  ] at hbad
  tauto

theorem fin15Anchored_clause23064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom3467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01922
  ] at hbad
  tauto

theorem fin15Anchored_clause23065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom3467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01922
  ] at hbad
  tauto

theorem fin15Anchored_clause23066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom3467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01922
  ] at hbad
  tauto

theorem fin15Anchored_clause23067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3467 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom3467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01922
  ] at hbad
  tauto

theorem fin15Anchored_clause23068 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3467 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom1051 Fin15AnchoredAtom1056
    Fin15AnchoredAtom1071 Fin15AnchoredAtom1751 Fin15AnchoredAtom3467 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01922
  ] at hbad
  tauto

theorem fin15Anchored_clause23069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom3469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04994
  ] at hbad
  tauto

theorem fin15Anchored_clause23070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom3469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04994
  ] at hbad
  tauto

theorem fin15Anchored_clause23071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom3469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04994
  ] at hbad
  tauto

theorem fin15Anchored_clause23072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom3469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04994
  ] at hbad
  tauto

theorem fin15Anchored_clause23073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3469 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom3469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04994
  ] at hbad
  tauto

theorem fin15Anchored_clause23074 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3469 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom1053 Fin15AnchoredAtom1058
    Fin15AnchoredAtom1073 Fin15AnchoredAtom1753 Fin15AnchoredAtom3469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04994
  ] at hbad
  tauto

theorem fin15Anchored_clause23075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom3470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09090
  ] at hbad
  tauto

theorem fin15Anchored_clause23076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom3470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09090
  ] at hbad
  tauto

theorem fin15Anchored_clause23077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom3470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09090
  ] at hbad
  tauto

theorem fin15Anchored_clause23078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3470 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom3470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09090
  ] at hbad
  tauto

theorem fin15Anchored_clause23079 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3470 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom1054 Fin15AnchoredAtom1059
    Fin15AnchoredAtom1074 Fin15AnchoredAtom1754 Fin15AnchoredAtom3470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09090
  ] at hbad
  tauto

theorem fin15Anchored_clause23080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom3471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17282
  ] at hbad
  tauto

theorem fin15Anchored_clause23081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom3471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17282
  ] at hbad
  tauto

theorem fin15Anchored_clause23082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1075 Fin15AnchoredAtom3471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17282
  ] at hbad
  tauto

theorem fin15Anchored_clause23083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3471 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1755 Fin15AnchoredAtom3471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17282
  ] at hbad
  tauto

theorem fin15Anchored_clause23084 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3471 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1075 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom1055 Fin15AnchoredAtom1060
    Fin15AnchoredAtom1075 Fin15AnchoredAtom1755 Fin15AnchoredAtom3471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17282
  ] at hbad
  tauto

theorem fin15Anchored_clause23085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom3473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05506
  ] at hbad
  tauto

theorem fin15Anchored_clause23086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom3473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05506
  ] at hbad
  tauto

theorem fin15Anchored_clause23087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom3473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05506
  ] at hbad
  tauto

theorem fin15Anchored_clause23088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3473 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom3473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05506
  ] at hbad
  tauto

theorem fin15Anchored_clause23089 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3473 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom1053 Fin15AnchoredAtom1062
    Fin15AnchoredAtom1077 Fin15AnchoredAtom1757 Fin15AnchoredAtom3473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05506
  ] at hbad
  tauto

theorem fin15Anchored_clause23090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom3474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09602
  ] at hbad
  tauto

theorem fin15Anchored_clause23091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom3474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09602
  ] at hbad
  tauto

theorem fin15Anchored_clause23092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom3474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09602
  ] at hbad
  tauto

theorem fin15Anchored_clause23093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom3474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09602
  ] at hbad
  tauto

theorem fin15Anchored_clause23094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3474 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom3474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09602
  ] at hbad
  tauto

theorem fin15Anchored_clause23095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom3475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17794
  ] at hbad
  tauto

theorem fin15Anchored_clause23096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1055 Fin15AnchoredAtom3475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17794
  ] at hbad
  tauto

theorem fin15Anchored_clause23097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17794
  ] at hbad
  tauto

theorem fin15Anchored_clause23098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3475 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1759 Fin15AnchoredAtom3475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17794
  ] at hbad
  tauto

theorem fin15Anchored_clause23099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom3479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12674
  ] at hbad
  tauto

theorem fin15Anchored_clause23100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom3479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12674
  ] at hbad
  tauto

theorem fin15Anchored_clause23101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12674
  ] at hbad
  tauto

theorem fin15Anchored_clause23102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1083 Fin15AnchoredAtom3479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12674
  ] at hbad
  tauto

theorem fin15Anchored_clause23103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3479 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom3479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12674
  ] at hbad
  tauto

theorem fin15Anchored_clause23104 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3479 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom1054 Fin15AnchoredAtom1068
    Fin15AnchoredAtom1083 Fin15AnchoredAtom1763 Fin15AnchoredAtom3479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12674
  ] at hbad
  tauto

theorem fin15Anchored_clause23105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom3480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20866
  ] at hbad
  tauto

theorem fin15Anchored_clause23106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1055 Fin15AnchoredAtom3480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20866
  ] at hbad
  tauto

theorem fin15Anchored_clause23107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20866
  ] at hbad
  tauto

theorem fin15Anchored_clause23108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1084 Fin15AnchoredAtom3480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20866
  ] at hbad
  tauto

theorem fin15Anchored_clause23109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3480 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1764 Fin15AnchoredAtom3480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20866
  ] at hbad
  tauto

theorem fin15Anchored_clause23110 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3480 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom1055 Fin15AnchoredAtom1069
    Fin15AnchoredAtom1084 Fin15AnchoredAtom1764 Fin15AnchoredAtom3480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20866
  ] at hbad
  tauto

theorem fin15Anchored_clause23111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom3481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24962
  ] at hbad
  tauto

theorem fin15Anchored_clause23112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1055 Fin15AnchoredAtom3481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24962
  ] at hbad
  tauto

theorem fin15Anchored_clause23113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24962
  ] at hbad
  tauto

theorem fin15Anchored_clause23114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1085 Fin15AnchoredAtom3481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24962
  ] at hbad
  tauto

theorem fin15Anchored_clause23115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3481 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1765 Fin15AnchoredAtom3481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24962
  ] at hbad
  tauto

theorem fin15Anchored_clause23116 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3481 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom1055 Fin15AnchoredAtom1070
    Fin15AnchoredAtom1085 Fin15AnchoredAtom1765 Fin15AnchoredAtom3481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24962
  ] at hbad
  tauto

theorem fin15Anchored_clause23117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3482 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom3482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03714
  ] at hbad
  tauto

theorem fin15Anchored_clause23118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3482 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom3482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03714
  ] at hbad
  tauto

theorem fin15Anchored_clause23119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom3483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05762
  ] at hbad
  tauto

theorem fin15Anchored_clause23120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom3483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05762
  ] at hbad
  tauto

theorem fin15Anchored_clause23121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom3483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05762
  ] at hbad
  tauto

theorem fin15Anchored_clause23122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05762
  ] at hbad
  tauto

theorem fin15Anchored_clause23123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3483 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom3483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05762
  ] at hbad
  tauto

theorem fin15Anchored_clause23124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom1058 Fin15AnchoredAtom1062
    Fin15AnchoredAtom1087 Fin15AnchoredAtom1767 Fin15AnchoredAtom3483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05762
  ] at hbad
  tauto

theorem fin15Anchored_clause23125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom3484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09858
  ] at hbad
  tauto

theorem fin15Anchored_clause23126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom3484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09858
  ] at hbad
  tauto

theorem fin15Anchored_clause23127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom3484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09858
  ] at hbad
  tauto

theorem fin15Anchored_clause23128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09858
  ] at hbad
  tauto

theorem fin15Anchored_clause23129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3484 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom3484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09858
  ] at hbad
  tauto

theorem fin15Anchored_clause23130 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom1059 Fin15AnchoredAtom1063
    Fin15AnchoredAtom1088 Fin15AnchoredAtom1768 Fin15AnchoredAtom3484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09858
  ] at hbad
  tauto

theorem fin15Anchored_clause23131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom3485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18050
  ] at hbad
  tauto

theorem fin15Anchored_clause23132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom3485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18050
  ] at hbad
  tauto

theorem fin15Anchored_clause23133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18050
  ] at hbad
  tauto

theorem fin15Anchored_clause23134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom3485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18050
  ] at hbad
  tauto

theorem fin15Anchored_clause23135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3485 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom3485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18050
  ] at hbad
  tauto

theorem fin15Anchored_clause23136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom1060 Fin15AnchoredAtom1064
    Fin15AnchoredAtom1089 Fin15AnchoredAtom1769 Fin15AnchoredAtom3485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18050
  ] at hbad
  tauto

theorem fin15Anchored_clause23137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom3486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06786
  ] at hbad
  tauto

theorem fin15Anchored_clause23138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1065 Fin15AnchoredAtom3486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06786
  ] at hbad
  tauto

theorem fin15Anchored_clause23139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3486 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1770 Fin15AnchoredAtom3486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06786
  ] at hbad
  tauto

theorem fin15Anchored_clause23140 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3486 chi ∧
      Fin15AnchoredAtom1057 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1065 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1057 Fin15AnchoredAtom1058 Fin15AnchoredAtom1065
    Fin15AnchoredAtom1090 Fin15AnchoredAtom1770 Fin15AnchoredAtom3486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06786
  ] at hbad
  tauto

theorem fin15Anchored_clause23141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3487 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom3487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10882
  ] at hbad
  tauto

theorem fin15Anchored_clause23142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3488 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom3488 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19074
  ] at hbad
  tauto

theorem fin15Anchored_clause23143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3488 chi ∧
      ¬Fin15AnchoredAtom1067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1067 Fin15AnchoredAtom3488 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19074
  ] at hbad
  tauto

theorem fin15Anchored_clause23144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom3489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12930
  ] at hbad
  tauto

theorem fin15Anchored_clause23145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom3489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12930
  ] at hbad
  tauto

theorem fin15Anchored_clause23146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12930
  ] at hbad
  tauto

theorem fin15Anchored_clause23147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12930
  ] at hbad
  tauto

theorem fin15Anchored_clause23148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3489 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom3489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12930
  ] at hbad
  tauto

theorem fin15Anchored_clause23149 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom1059 Fin15AnchoredAtom1068
    Fin15AnchoredAtom1093 Fin15AnchoredAtom1773 Fin15AnchoredAtom3489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12930
  ] at hbad
  tauto

theorem fin15Anchored_clause23150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom3490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21122
  ] at hbad
  tauto

theorem fin15Anchored_clause23151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom3490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21122
  ] at hbad
  tauto

theorem fin15Anchored_clause23152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21122
  ] at hbad
  tauto

theorem fin15Anchored_clause23153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21122
  ] at hbad
  tauto

theorem fin15Anchored_clause23154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3490 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom3490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21122
  ] at hbad
  tauto

theorem fin15Anchored_clause23155 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom1060 Fin15AnchoredAtom1069
    Fin15AnchoredAtom1094 Fin15AnchoredAtom1774 Fin15AnchoredAtom3490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21122
  ] at hbad
  tauto

theorem fin15Anchored_clause23156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom3491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25218
  ] at hbad
  tauto

theorem fin15Anchored_clause23157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom3491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25218
  ] at hbad
  tauto

theorem fin15Anchored_clause23158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25218
  ] at hbad
  tauto

theorem fin15Anchored_clause23159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom3491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25218
  ] at hbad
  tauto

theorem fin15Anchored_clause23160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3491 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom3491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25218
  ] at hbad
  tauto

theorem fin15Anchored_clause23161 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom1060 Fin15AnchoredAtom1070
    Fin15AnchoredAtom1095 Fin15AnchoredAtom1775 Fin15AnchoredAtom3491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25218
  ] at hbad
  tauto

theorem fin15Anchored_clause23162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom3492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07298
  ] at hbad
  tauto

theorem fin15Anchored_clause23163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1096 Fin15AnchoredAtom3492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07298
  ] at hbad
  tauto

theorem fin15Anchored_clause23164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3492 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom3492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07298
  ] at hbad
  tauto

theorem fin15Anchored_clause23165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3493 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom3493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11394
  ] at hbad
  tauto

theorem fin15Anchored_clause23166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3494 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3494 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19586
  ] at hbad
  tauto

theorem fin15Anchored_clause23167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom3495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13442
  ] at hbad
  tauto

end ErdosSzekeres

end
