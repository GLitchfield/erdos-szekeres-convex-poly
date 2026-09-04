module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 175. -/

theorem fin15Anchored_clause22400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom3308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05650
  ] at hbad
  tauto

theorem fin15Anchored_clause22401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05650
  ] at hbad
  tauto

theorem fin15Anchored_clause22402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom3308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05650
  ] at hbad
  tauto

theorem fin15Anchored_clause22403 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom0973 Fin15AnchoredAtom0977
    Fin15AnchoredAtom1087 Fin15AnchoredAtom1592 Fin15AnchoredAtom3308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05650
  ] at hbad
  tauto

theorem fin15Anchored_clause22404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom3309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09746
  ] at hbad
  tauto

theorem fin15Anchored_clause22405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom3309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09746
  ] at hbad
  tauto

theorem fin15Anchored_clause22406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom3309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09746
  ] at hbad
  tauto

theorem fin15Anchored_clause22407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09746
  ] at hbad
  tauto

theorem fin15Anchored_clause22408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom3309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09746
  ] at hbad
  tauto

theorem fin15Anchored_clause22409 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom0974 Fin15AnchoredAtom0978
    Fin15AnchoredAtom1088 Fin15AnchoredAtom1593 Fin15AnchoredAtom3309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09746
  ] at hbad
  tauto

theorem fin15Anchored_clause22410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom3310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17938
  ] at hbad
  tauto

theorem fin15Anchored_clause22411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom3310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17938
  ] at hbad
  tauto

theorem fin15Anchored_clause22412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom3310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17938
  ] at hbad
  tauto

theorem fin15Anchored_clause22413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom3310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17938
  ] at hbad
  tauto

theorem fin15Anchored_clause22414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom3310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17938
  ] at hbad
  tauto

theorem fin15Anchored_clause22415 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom0975 Fin15AnchoredAtom0979
    Fin15AnchoredAtom1089 Fin15AnchoredAtom1594 Fin15AnchoredAtom3310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17938
  ] at hbad
  tauto

theorem fin15Anchored_clause22416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3311 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom3311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06674
  ] at hbad
  tauto

theorem fin15Anchored_clause22417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3311 chi ∧
      ¬Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0980 Fin15AnchoredAtom3311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06674
  ] at hbad
  tauto

theorem fin15Anchored_clause22418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3311 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1595 Fin15AnchoredAtom3311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06674
  ] at hbad
  tauto

theorem fin15Anchored_clause22419 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3311 chi ∧
      Fin15AnchoredAtom0972 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0972 Fin15AnchoredAtom0973 Fin15AnchoredAtom0980
    Fin15AnchoredAtom1090 Fin15AnchoredAtom1595 Fin15AnchoredAtom3311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06674
  ] at hbad
  tauto

theorem fin15Anchored_clause22420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3312 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom3312 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10770
  ] at hbad
  tauto

theorem fin15Anchored_clause22421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3312 chi ∧
      ¬Fin15AnchoredAtom0981 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0981 Fin15AnchoredAtom3312 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10770
  ] at hbad
  tauto

theorem fin15Anchored_clause22422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3312 chi ∧
      ¬Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1596 Fin15AnchoredAtom3312 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10770
  ] at hbad
  tauto

theorem fin15Anchored_clause22423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3313 chi ∧
      ¬Fin15AnchoredAtom0982 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0982 Fin15AnchoredAtom3313 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18962
  ] at hbad
  tauto

theorem fin15Anchored_clause22424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3313 chi ∧
      ¬Fin15AnchoredAtom1092 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1092 Fin15AnchoredAtom3313 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18962
  ] at hbad
  tauto

theorem fin15Anchored_clause22425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3313 chi ∧
      ¬Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1597 Fin15AnchoredAtom3313 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18962
  ] at hbad
  tauto

theorem fin15Anchored_clause22426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom3314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12818
  ] at hbad
  tauto

theorem fin15Anchored_clause22427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom3314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12818
  ] at hbad
  tauto

theorem fin15Anchored_clause22428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom3314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12818
  ] at hbad
  tauto

theorem fin15Anchored_clause22429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12818
  ] at hbad
  tauto

theorem fin15Anchored_clause22430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom3314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12818
  ] at hbad
  tauto

theorem fin15Anchored_clause22431 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom0974 Fin15AnchoredAtom0983
    Fin15AnchoredAtom1093 Fin15AnchoredAtom1598 Fin15AnchoredAtom3314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12818
  ] at hbad
  tauto

theorem fin15Anchored_clause22432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom3315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21010
  ] at hbad
  tauto

theorem fin15Anchored_clause22433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom3315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21010
  ] at hbad
  tauto

theorem fin15Anchored_clause22434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom3315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21010
  ] at hbad
  tauto

theorem fin15Anchored_clause22435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21010
  ] at hbad
  tauto

theorem fin15Anchored_clause22436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom3315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21010
  ] at hbad
  tauto

theorem fin15Anchored_clause22437 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom0975 Fin15AnchoredAtom0984
    Fin15AnchoredAtom1094 Fin15AnchoredAtom1599 Fin15AnchoredAtom3315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21010
  ] at hbad
  tauto

theorem fin15Anchored_clause22438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom3316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25106
  ] at hbad
  tauto

theorem fin15Anchored_clause22439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom3316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25106
  ] at hbad
  tauto

theorem fin15Anchored_clause22440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom3316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25106
  ] at hbad
  tauto

theorem fin15Anchored_clause22441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom3316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25106
  ] at hbad
  tauto

theorem fin15Anchored_clause22442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom3316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25106
  ] at hbad
  tauto

theorem fin15Anchored_clause22443 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom0975 Fin15AnchoredAtom0985
    Fin15AnchoredAtom1095 Fin15AnchoredAtom1600 Fin15AnchoredAtom3316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25106
  ] at hbad
  tauto

theorem fin15Anchored_clause22444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom3317 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07186
  ] at hbad
  tauto

theorem fin15Anchored_clause22445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0980 Fin15AnchoredAtom3317 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07186
  ] at hbad
  tauto

theorem fin15Anchored_clause22446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3317 chi ∧
      ¬Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1096 Fin15AnchoredAtom3317 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07186
  ] at hbad
  tauto

theorem fin15Anchored_clause22447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3318 chi ∧
      ¬Fin15AnchoredAtom0981 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0981 Fin15AnchoredAtom3318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11282
  ] at hbad
  tauto

theorem fin15Anchored_clause22448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3318 chi ∧
      ¬Fin15AnchoredAtom1097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1097 Fin15AnchoredAtom3318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11282
  ] at hbad
  tauto

theorem fin15Anchored_clause22449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3318 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1602 Fin15AnchoredAtom3318 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11282
  ] at hbad
  tauto

theorem fin15Anchored_clause22450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3319 chi ∧
      ¬Fin15AnchoredAtom1098 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1098 Fin15AnchoredAtom3319 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19474
  ] at hbad
  tauto

theorem fin15Anchored_clause22451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom3320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13330
  ] at hbad
  tauto

theorem fin15Anchored_clause22452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom3320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13330
  ] at hbad
  tauto

theorem fin15Anchored_clause22453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom3320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13330
  ] at hbad
  tauto

theorem fin15Anchored_clause22454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13330
  ] at hbad
  tauto

theorem fin15Anchored_clause22455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom3320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13330
  ] at hbad
  tauto

theorem fin15Anchored_clause22456 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom0978 Fin15AnchoredAtom0983
    Fin15AnchoredAtom1099 Fin15AnchoredAtom1604 Fin15AnchoredAtom3320 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13330
  ] at hbad
  tauto

theorem fin15Anchored_clause22457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom3321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21522
  ] at hbad
  tauto

theorem fin15Anchored_clause22458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom3321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21522
  ] at hbad
  tauto

theorem fin15Anchored_clause22459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom3321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21522
  ] at hbad
  tauto

theorem fin15Anchored_clause22460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21522
  ] at hbad
  tauto

theorem fin15Anchored_clause22461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom3321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21522
  ] at hbad
  tauto

theorem fin15Anchored_clause22462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom0979 Fin15AnchoredAtom0984
    Fin15AnchoredAtom1100 Fin15AnchoredAtom1605 Fin15AnchoredAtom3321 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21522
  ] at hbad
  tauto

theorem fin15Anchored_clause22463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom3322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25618
  ] at hbad
  tauto

theorem fin15Anchored_clause22464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom3322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25618
  ] at hbad
  tauto

theorem fin15Anchored_clause22465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom3322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25618
  ] at hbad
  tauto

theorem fin15Anchored_clause22466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25618
  ] at hbad
  tauto

theorem fin15Anchored_clause22467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom3322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25618
  ] at hbad
  tauto

theorem fin15Anchored_clause22468 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom0979 Fin15AnchoredAtom0985
    Fin15AnchoredAtom1101 Fin15AnchoredAtom1606 Fin15AnchoredAtom3322 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25618
  ] at hbad
  tauto

theorem fin15Anchored_clause22469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom0981 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0981 Fin15AnchoredAtom3323 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14354
  ] at hbad
  tauto

theorem fin15Anchored_clause22470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom3323 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14354
  ] at hbad
  tauto

theorem fin15Anchored_clause22471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom1102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1102 Fin15AnchoredAtom3323 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14354
  ] at hbad
  tauto

theorem fin15Anchored_clause22472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3323 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1607 Fin15AnchoredAtom3323 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14354
  ] at hbad
  tauto

theorem fin15Anchored_clause22473 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3323 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom0981 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom1102 chi ∧
      Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0980 Fin15AnchoredAtom0981 Fin15AnchoredAtom0983
    Fin15AnchoredAtom1102 Fin15AnchoredAtom1607 Fin15AnchoredAtom3323 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14354
  ] at hbad
  tauto

theorem fin15Anchored_clause22474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3324 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom3324 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22546
  ] at hbad
  tauto

theorem fin15Anchored_clause22475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3324 chi ∧
      ¬Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1103 Fin15AnchoredAtom3324 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22546
  ] at hbad
  tauto

theorem fin15Anchored_clause22476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom3326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28690
  ] at hbad
  tauto

theorem fin15Anchored_clause22477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0984 Fin15AnchoredAtom3326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28690
  ] at hbad
  tauto

theorem fin15Anchored_clause22478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0985 Fin15AnchoredAtom3326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28690
  ] at hbad
  tauto

theorem fin15Anchored_clause22479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28690
  ] at hbad
  tauto

theorem fin15Anchored_clause22480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom3326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28690
  ] at hbad
  tauto

theorem fin15Anchored_clause22481 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom0983 chi ∧
      Fin15AnchoredAtom0984 chi ∧
      Fin15AnchoredAtom0985 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom0984 Fin15AnchoredAtom0985
    Fin15AnchoredAtom1105 Fin15AnchoredAtom1610 Fin15AnchoredAtom3326 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28690
  ] at hbad
  tauto

theorem fin15Anchored_clause22482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom3327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00482
  ] at hbad
  tauto

theorem fin15Anchored_clause22483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom3327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00482
  ] at hbad
  tauto

theorem fin15Anchored_clause22484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom3327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00482
  ] at hbad
  tauto

theorem fin15Anchored_clause22485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3327 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom3327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00482
  ] at hbad
  tauto

theorem fin15Anchored_clause22486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3327 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom0987 Fin15AnchoredAtom0994
    Fin15AnchoredAtom1022 Fin15AnchoredAtom1611 Fin15AnchoredAtom3327 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00482
  ] at hbad
  tauto

theorem fin15Anchored_clause22487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom3328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00738
  ] at hbad
  tauto

theorem fin15Anchored_clause22488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom3328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00738
  ] at hbad
  tauto

theorem fin15Anchored_clause22489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom3328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00738
  ] at hbad
  tauto

theorem fin15Anchored_clause22490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom3328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00738
  ] at hbad
  tauto

theorem fin15Anchored_clause22491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom3328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00738
  ] at hbad
  tauto

theorem fin15Anchored_clause22492 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom0988 Fin15AnchoredAtom0995
    Fin15AnchoredAtom1023 Fin15AnchoredAtom1612 Fin15AnchoredAtom3328 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00738
  ] at hbad
  tauto

theorem fin15Anchored_clause22493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom3329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01250
  ] at hbad
  tauto

theorem fin15Anchored_clause22494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom3329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01250
  ] at hbad
  tauto

theorem fin15Anchored_clause22495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom3329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01250
  ] at hbad
  tauto

theorem fin15Anchored_clause22496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom3329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01250
  ] at hbad
  tauto

theorem fin15Anchored_clause22497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom3329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01250
  ] at hbad
  tauto

theorem fin15Anchored_clause22498 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom0989 Fin15AnchoredAtom0996
    Fin15AnchoredAtom1024 Fin15AnchoredAtom1613 Fin15AnchoredAtom3329 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01250
  ] at hbad
  tauto

theorem fin15Anchored_clause22499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom3331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04322
  ] at hbad
  tauto

theorem fin15Anchored_clause22500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom3331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04322
  ] at hbad
  tauto

theorem fin15Anchored_clause22501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom3331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04322
  ] at hbad
  tauto

theorem fin15Anchored_clause22502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom3331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04322
  ] at hbad
  tauto

theorem fin15Anchored_clause22503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom3331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04322
  ] at hbad
  tauto

theorem fin15Anchored_clause22504 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom0991 Fin15AnchoredAtom0998
    Fin15AnchoredAtom1026 Fin15AnchoredAtom1615 Fin15AnchoredAtom3331 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04322
  ] at hbad
  tauto

theorem fin15Anchored_clause22505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom3332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08418
  ] at hbad
  tauto

theorem fin15Anchored_clause22506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom3332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08418
  ] at hbad
  tauto

theorem fin15Anchored_clause22507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom3332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08418
  ] at hbad
  tauto

theorem fin15Anchored_clause22508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom3332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08418
  ] at hbad
  tauto

theorem fin15Anchored_clause22509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom3332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08418
  ] at hbad
  tauto

theorem fin15Anchored_clause22510 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom0992 Fin15AnchoredAtom0999
    Fin15AnchoredAtom1027 Fin15AnchoredAtom1616 Fin15AnchoredAtom3332 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08418
  ] at hbad
  tauto

theorem fin15Anchored_clause22511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom3333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16610
  ] at hbad
  tauto

theorem fin15Anchored_clause22512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom3333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16610
  ] at hbad
  tauto

theorem fin15Anchored_clause22513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom3333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16610
  ] at hbad
  tauto

theorem fin15Anchored_clause22514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom3333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16610
  ] at hbad
  tauto

theorem fin15Anchored_clause22515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom3333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16610
  ] at hbad
  tauto

theorem fin15Anchored_clause22516 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom0986 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0986 Fin15AnchoredAtom0993 Fin15AnchoredAtom1000
    Fin15AnchoredAtom1028 Fin15AnchoredAtom1617 Fin15AnchoredAtom3333 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16610
  ] at hbad
  tauto

theorem fin15Anchored_clause22517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom3334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00866
  ] at hbad
  tauto

theorem fin15Anchored_clause22518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom3334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00866
  ] at hbad
  tauto

theorem fin15Anchored_clause22519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom3334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00866
  ] at hbad
  tauto

theorem fin15Anchored_clause22520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom3334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00866
  ] at hbad
  tauto

theorem fin15Anchored_clause22521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3334 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom3334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00866
  ] at hbad
  tauto

theorem fin15Anchored_clause22522 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3334 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom0988 Fin15AnchoredAtom1001
    Fin15AnchoredAtom1029 Fin15AnchoredAtom1618 Fin15AnchoredAtom3334 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00866
  ] at hbad
  tauto

theorem fin15Anchored_clause22523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom3335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01378
  ] at hbad
  tauto

theorem fin15Anchored_clause22524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom3335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01378
  ] at hbad
  tauto

theorem fin15Anchored_clause22525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom3335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01378
  ] at hbad
  tauto

theorem fin15Anchored_clause22526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom3335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01378
  ] at hbad
  tauto

theorem fin15Anchored_clause22527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3335 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom3335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01378
  ] at hbad
  tauto

end ErdosSzekeres

end
