module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 172. -/

theorem fin15Anchored_clause22016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom3223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01330
  ] at hbad
  tauto

theorem fin15Anchored_clause22017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3223 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom3223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01330
  ] at hbad
  tauto

theorem fin15Anchored_clause22018 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0966 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom0945 Fin15AnchoredAtom0966
    Fin15AnchoredAtom1002 Fin15AnchoredAtom1507 Fin15AnchoredAtom3223 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01330
  ] at hbad
  tauto

theorem fin15Anchored_clause22019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom3225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04402
  ] at hbad
  tauto

theorem fin15Anchored_clause22020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom3225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04402
  ] at hbad
  tauto

theorem fin15Anchored_clause22021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3225 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom3225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04402
  ] at hbad
  tauto

theorem fin15Anchored_clause22022 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3225 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0968 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom0947 Fin15AnchoredAtom0968
    Fin15AnchoredAtom1004 Fin15AnchoredAtom1509 Fin15AnchoredAtom3225 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04402
  ] at hbad
  tauto

theorem fin15Anchored_clause22023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom3226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08498
  ] at hbad
  tauto

theorem fin15Anchored_clause22024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom3226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08498
  ] at hbad
  tauto

theorem fin15Anchored_clause22025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom3226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08498
  ] at hbad
  tauto

theorem fin15Anchored_clause22026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom3226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08498
  ] at hbad
  tauto

theorem fin15Anchored_clause22027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3226 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom3226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08498
  ] at hbad
  tauto

theorem fin15Anchored_clause22028 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0969 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom0948 Fin15AnchoredAtom0969
    Fin15AnchoredAtom1005 Fin15AnchoredAtom1510 Fin15AnchoredAtom3226 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08498
  ] at hbad
  tauto

theorem fin15Anchored_clause22029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom3227 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16690
  ] at hbad
  tauto

theorem fin15Anchored_clause22030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom3227 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16690
  ] at hbad
  tauto

theorem fin15Anchored_clause22031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3227 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1511 Fin15AnchoredAtom3227 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16690
  ] at hbad
  tauto

theorem fin15Anchored_clause22032 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3227 chi ∧
      Fin15AnchoredAtom0943 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0943 Fin15AnchoredAtom0949 Fin15AnchoredAtom0970
    Fin15AnchoredAtom1006 Fin15AnchoredAtom1511 Fin15AnchoredAtom3227 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16690
  ] at hbad
  tauto

theorem fin15Anchored_clause22033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom3228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01586
  ] at hbad
  tauto

theorem fin15Anchored_clause22034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom3228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01586
  ] at hbad
  tauto

theorem fin15Anchored_clause22035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom3228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01586
  ] at hbad
  tauto

theorem fin15Anchored_clause22036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom3228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01586
  ] at hbad
  tauto

theorem fin15Anchored_clause22037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom3228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01586
  ] at hbad
  tauto

theorem fin15Anchored_clause22038 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom0945 Fin15AnchoredAtom0971
    Fin15AnchoredAtom1007 Fin15AnchoredAtom1512 Fin15AnchoredAtom3228 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01586
  ] at hbad
  tauto

theorem fin15Anchored_clause22039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3229 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom3229 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02610
  ] at hbad
  tauto

theorem fin15Anchored_clause22040 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3229 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0946 chi ∧
      Fin15AnchoredAtom0972 chi ∧
      Fin15AnchoredAtom1008 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom0946 Fin15AnchoredAtom0972
    Fin15AnchoredAtom1008 Fin15AnchoredAtom1513 Fin15AnchoredAtom3229 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02610
  ] at hbad
  tauto

theorem fin15Anchored_clause22041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom3230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04658
  ] at hbad
  tauto

theorem fin15Anchored_clause22042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom3230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04658
  ] at hbad
  tauto

theorem fin15Anchored_clause22043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom3230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04658
  ] at hbad
  tauto

theorem fin15Anchored_clause22044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom3230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04658
  ] at hbad
  tauto

theorem fin15Anchored_clause22045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom3230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04658
  ] at hbad
  tauto

theorem fin15Anchored_clause22046 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom0947 Fin15AnchoredAtom0973
    Fin15AnchoredAtom1009 Fin15AnchoredAtom1514 Fin15AnchoredAtom3230 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04658
  ] at hbad
  tauto

theorem fin15Anchored_clause22047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom3231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08754
  ] at hbad
  tauto

theorem fin15Anchored_clause22048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom3231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08754
  ] at hbad
  tauto

theorem fin15Anchored_clause22049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom3231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08754
  ] at hbad
  tauto

theorem fin15Anchored_clause22050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom3231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08754
  ] at hbad
  tauto

theorem fin15Anchored_clause22051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom3231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08754
  ] at hbad
  tauto

theorem fin15Anchored_clause22052 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom0948 Fin15AnchoredAtom0974
    Fin15AnchoredAtom1010 Fin15AnchoredAtom1515 Fin15AnchoredAtom3231 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08754
  ] at hbad
  tauto

theorem fin15Anchored_clause22053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom3232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16946
  ] at hbad
  tauto

theorem fin15Anchored_clause22054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom3232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16946
  ] at hbad
  tauto

theorem fin15Anchored_clause22055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom3232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16946
  ] at hbad
  tauto

theorem fin15Anchored_clause22056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom3232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16946
  ] at hbad
  tauto

theorem fin15Anchored_clause22057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom3232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16946
  ] at hbad
  tauto

theorem fin15Anchored_clause22058 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom0949 Fin15AnchoredAtom0975
    Fin15AnchoredAtom1011 Fin15AnchoredAtom1516 Fin15AnchoredAtom3232 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16946
  ] at hbad
  tauto

theorem fin15Anchored_clause22059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom3233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03122
  ] at hbad
  tauto

theorem fin15Anchored_clause22060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom0946 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0946 Fin15AnchoredAtom3233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03122
  ] at hbad
  tauto

theorem fin15Anchored_clause22061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3233 chi ∧
      ¬Fin15AnchoredAtom1012 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1012 Fin15AnchoredAtom3233 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03122
  ] at hbad
  tauto

theorem fin15Anchored_clause22062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom3234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05170
  ] at hbad
  tauto

theorem fin15Anchored_clause22063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom3234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05170
  ] at hbad
  tauto

theorem fin15Anchored_clause22064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom3234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05170
  ] at hbad
  tauto

theorem fin15Anchored_clause22065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom3234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05170
  ] at hbad
  tauto

theorem fin15Anchored_clause22066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom3234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05170
  ] at hbad
  tauto

theorem fin15Anchored_clause22067 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom0947 Fin15AnchoredAtom0977
    Fin15AnchoredAtom1013 Fin15AnchoredAtom1518 Fin15AnchoredAtom3234 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05170
  ] at hbad
  tauto

theorem fin15Anchored_clause22068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom3235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09266
  ] at hbad
  tauto

theorem fin15Anchored_clause22069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom3235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09266
  ] at hbad
  tauto

theorem fin15Anchored_clause22070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom3235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09266
  ] at hbad
  tauto

theorem fin15Anchored_clause22071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom3235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09266
  ] at hbad
  tauto

theorem fin15Anchored_clause22072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom3235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09266
  ] at hbad
  tauto

theorem fin15Anchored_clause22073 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom0948 Fin15AnchoredAtom0978
    Fin15AnchoredAtom1014 Fin15AnchoredAtom1519 Fin15AnchoredAtom3235 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09266
  ] at hbad
  tauto

theorem fin15Anchored_clause22074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom3236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17458
  ] at hbad
  tauto

theorem fin15Anchored_clause22075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom3236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17458
  ] at hbad
  tauto

theorem fin15Anchored_clause22076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom3236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17458
  ] at hbad
  tauto

theorem fin15Anchored_clause22077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom3236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17458
  ] at hbad
  tauto

theorem fin15Anchored_clause22078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom3236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17458
  ] at hbad
  tauto

theorem fin15Anchored_clause22079 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom0949 Fin15AnchoredAtom0979
    Fin15AnchoredAtom1015 Fin15AnchoredAtom1520 Fin15AnchoredAtom3236 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17458
  ] at hbad
  tauto

theorem fin15Anchored_clause22080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3237 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom3237 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06194
  ] at hbad
  tauto

theorem fin15Anchored_clause22081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3238 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom3238 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10290
  ] at hbad
  tauto

theorem fin15Anchored_clause22082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3239 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom3239 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18482
  ] at hbad
  tauto

theorem fin15Anchored_clause22083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom3240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12338
  ] at hbad
  tauto

theorem fin15Anchored_clause22084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom3240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12338
  ] at hbad
  tauto

theorem fin15Anchored_clause22085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom3240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12338
  ] at hbad
  tauto

theorem fin15Anchored_clause22086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom3240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12338
  ] at hbad
  tauto

theorem fin15Anchored_clause22087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom3240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12338
  ] at hbad
  tauto

theorem fin15Anchored_clause22088 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom0948 Fin15AnchoredAtom0983
    Fin15AnchoredAtom1019 Fin15AnchoredAtom1524 Fin15AnchoredAtom3240 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12338
  ] at hbad
  tauto

theorem fin15Anchored_clause22089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom3241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20530
  ] at hbad
  tauto

theorem fin15Anchored_clause22090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom3241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20530
  ] at hbad
  tauto

theorem fin15Anchored_clause22091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom3241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20530
  ] at hbad
  tauto

theorem fin15Anchored_clause22092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom3241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20530
  ] at hbad
  tauto

theorem fin15Anchored_clause22093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom3241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20530
  ] at hbad
  tauto

theorem fin15Anchored_clause22094 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom0949 Fin15AnchoredAtom0984
    Fin15AnchoredAtom1020 Fin15AnchoredAtom1525 Fin15AnchoredAtom3241 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20530
  ] at hbad
  tauto

theorem fin15Anchored_clause22095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom3242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24626
  ] at hbad
  tauto

theorem fin15Anchored_clause22096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom3242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24626
  ] at hbad
  tauto

theorem fin15Anchored_clause22097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom3242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24626
  ] at hbad
  tauto

theorem fin15Anchored_clause22098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom3242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24626
  ] at hbad
  tauto

theorem fin15Anchored_clause22099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom3242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24626
  ] at hbad
  tauto

theorem fin15Anchored_clause22100 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom0949 Fin15AnchoredAtom0985
    Fin15AnchoredAtom1021 Fin15AnchoredAtom1526 Fin15AnchoredAtom3242 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24626
  ] at hbad
  tauto

theorem fin15Anchored_clause22101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom3243 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00466
  ] at hbad
  tauto

theorem fin15Anchored_clause22102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom3243 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00466
  ] at hbad
  tauto

theorem fin15Anchored_clause22103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0958 Fin15AnchoredAtom3243 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00466
  ] at hbad
  tauto

theorem fin15Anchored_clause22104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3243 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom3243 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00466
  ] at hbad
  tauto

theorem fin15Anchored_clause22105 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3243 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0958 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom0951 Fin15AnchoredAtom0958
    Fin15AnchoredAtom1022 Fin15AnchoredAtom1527 Fin15AnchoredAtom3243 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00466
  ] at hbad
  tauto

theorem fin15Anchored_clause22106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom3244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00722
  ] at hbad
  tauto

theorem fin15Anchored_clause22107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom3244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00722
  ] at hbad
  tauto

theorem fin15Anchored_clause22108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom3244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00722
  ] at hbad
  tauto

theorem fin15Anchored_clause22109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom3244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00722
  ] at hbad
  tauto

theorem fin15Anchored_clause22110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom3244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00722
  ] at hbad
  tauto

theorem fin15Anchored_clause22111 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom0952 Fin15AnchoredAtom0959
    Fin15AnchoredAtom1023 Fin15AnchoredAtom1528 Fin15AnchoredAtom3244 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00722
  ] at hbad
  tauto

theorem fin15Anchored_clause22112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom3245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01234
  ] at hbad
  tauto

theorem fin15Anchored_clause22113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom3245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01234
  ] at hbad
  tauto

theorem fin15Anchored_clause22114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom3245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01234
  ] at hbad
  tauto

theorem fin15Anchored_clause22115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom3245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01234
  ] at hbad
  tauto

theorem fin15Anchored_clause22116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom3245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01234
  ] at hbad
  tauto

theorem fin15Anchored_clause22117 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom0953 Fin15AnchoredAtom0960
    Fin15AnchoredAtom1024 Fin15AnchoredAtom1529 Fin15AnchoredAtom3245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01234
  ] at hbad
  tauto

theorem fin15Anchored_clause22118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3246 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom3246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02258
  ] at hbad
  tauto

theorem fin15Anchored_clause22119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3246 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1530 Fin15AnchoredAtom3246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02258
  ] at hbad
  tauto

theorem fin15Anchored_clause22120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom3247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04306
  ] at hbad
  tauto

theorem fin15Anchored_clause22121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom3247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04306
  ] at hbad
  tauto

theorem fin15Anchored_clause22122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom3247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04306
  ] at hbad
  tauto

theorem fin15Anchored_clause22123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom3247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04306
  ] at hbad
  tauto

theorem fin15Anchored_clause22124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom3247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04306
  ] at hbad
  tauto

theorem fin15Anchored_clause22125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom0955 Fin15AnchoredAtom0962
    Fin15AnchoredAtom1026 Fin15AnchoredAtom1531 Fin15AnchoredAtom3247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04306
  ] at hbad
  tauto

theorem fin15Anchored_clause22126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom3248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08402
  ] at hbad
  tauto

theorem fin15Anchored_clause22127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom3248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08402
  ] at hbad
  tauto

theorem fin15Anchored_clause22128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom3248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08402
  ] at hbad
  tauto

theorem fin15Anchored_clause22129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom3248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08402
  ] at hbad
  tauto

theorem fin15Anchored_clause22130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom3248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08402
  ] at hbad
  tauto

theorem fin15Anchored_clause22131 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom0956 Fin15AnchoredAtom0963
    Fin15AnchoredAtom1027 Fin15AnchoredAtom1532 Fin15AnchoredAtom3248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08402
  ] at hbad
  tauto

theorem fin15Anchored_clause22132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom3249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16594
  ] at hbad
  tauto

theorem fin15Anchored_clause22133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom3249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16594
  ] at hbad
  tauto

theorem fin15Anchored_clause22134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom3249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16594
  ] at hbad
  tauto

theorem fin15Anchored_clause22135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom3249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16594
  ] at hbad
  tauto

theorem fin15Anchored_clause22136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom3249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16594
  ] at hbad
  tauto

theorem fin15Anchored_clause22137 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom0957 Fin15AnchoredAtom0964
    Fin15AnchoredAtom1028 Fin15AnchoredAtom1533 Fin15AnchoredAtom3249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16594
  ] at hbad
  tauto

theorem fin15Anchored_clause22138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom3250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00850
  ] at hbad
  tauto

theorem fin15Anchored_clause22139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom3250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00850
  ] at hbad
  tauto

theorem fin15Anchored_clause22140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom3250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00850
  ] at hbad
  tauto

theorem fin15Anchored_clause22141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom3250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00850
  ] at hbad
  tauto

theorem fin15Anchored_clause22142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3250 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom3250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00850
  ] at hbad
  tauto

theorem fin15Anchored_clause22143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom0951 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom0952 Fin15AnchoredAtom0965
    Fin15AnchoredAtom1029 Fin15AnchoredAtom1534 Fin15AnchoredAtom3250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00850
  ] at hbad
  tauto

end ErdosSzekeres

end
