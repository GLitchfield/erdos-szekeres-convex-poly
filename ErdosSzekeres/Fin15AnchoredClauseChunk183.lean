module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 183. -/

theorem fin15Anchored_clause23424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom3567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01564
  ] at hbad
  tauto

theorem fin15Anchored_clause23425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom3567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01564
  ] at hbad
  tauto

theorem fin15Anchored_clause23426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom3567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01564
  ] at hbad
  tauto

theorem fin15Anchored_clause23427 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom1111 Fin15AnchoredAtom1146
    Fin15AnchoredAtom1191 Fin15AnchoredAtom1356 Fin15AnchoredAtom3567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01564
  ] at hbad
  tauto

theorem fin15Anchored_clause23428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3568 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom3568 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02588
  ] at hbad
  tauto

theorem fin15Anchored_clause23429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom3569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04636
  ] at hbad
  tauto

theorem fin15Anchored_clause23430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom3569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04636
  ] at hbad
  tauto

theorem fin15Anchored_clause23431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom3569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04636
  ] at hbad
  tauto

theorem fin15Anchored_clause23432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom3569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04636
  ] at hbad
  tauto

theorem fin15Anchored_clause23433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom3569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04636
  ] at hbad
  tauto

theorem fin15Anchored_clause23434 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom1113 Fin15AnchoredAtom1148
    Fin15AnchoredAtom1193 Fin15AnchoredAtom1358 Fin15AnchoredAtom3569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04636
  ] at hbad
  tauto

theorem fin15Anchored_clause23435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom3570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08732
  ] at hbad
  tauto

theorem fin15Anchored_clause23436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom3570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08732
  ] at hbad
  tauto

theorem fin15Anchored_clause23437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom3570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08732
  ] at hbad
  tauto

theorem fin15Anchored_clause23438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom3570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08732
  ] at hbad
  tauto

theorem fin15Anchored_clause23439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom3570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08732
  ] at hbad
  tauto

theorem fin15Anchored_clause23440 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom1114 Fin15AnchoredAtom1149
    Fin15AnchoredAtom1194 Fin15AnchoredAtom1359 Fin15AnchoredAtom3570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08732
  ] at hbad
  tauto

theorem fin15Anchored_clause23441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom3571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16924
  ] at hbad
  tauto

theorem fin15Anchored_clause23442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom3571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16924
  ] at hbad
  tauto

theorem fin15Anchored_clause23443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom3571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16924
  ] at hbad
  tauto

theorem fin15Anchored_clause23444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom3571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16924
  ] at hbad
  tauto

theorem fin15Anchored_clause23445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom3571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16924
  ] at hbad
  tauto

theorem fin15Anchored_clause23446 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom1110 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1110 Fin15AnchoredAtom1115 Fin15AnchoredAtom1150
    Fin15AnchoredAtom1195 Fin15AnchoredAtom1360 Fin15AnchoredAtom3571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16924
  ] at hbad
  tauto

theorem fin15Anchored_clause23447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom3572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03100
  ] at hbad
  tauto

theorem fin15Anchored_clause23448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1112 Fin15AnchoredAtom3572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03100
  ] at hbad
  tauto

theorem fin15Anchored_clause23449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1151 Fin15AnchoredAtom3572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03100
  ] at hbad
  tauto

theorem fin15Anchored_clause23450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1196 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1196 Fin15AnchoredAtom3572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03100
  ] at hbad
  tauto

theorem fin15Anchored_clause23451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3572 chi ∧
      ¬Fin15AnchoredAtom1361 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1361 Fin15AnchoredAtom3572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03100
  ] at hbad
  tauto

theorem fin15Anchored_clause23452 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3572 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1112 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1196 chi ∧
      Fin15AnchoredAtom1361 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom1112 Fin15AnchoredAtom1151
    Fin15AnchoredAtom1196 Fin15AnchoredAtom1361 Fin15AnchoredAtom3572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03100
  ] at hbad
  tauto

theorem fin15Anchored_clause23453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom3573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05148
  ] at hbad
  tauto

theorem fin15Anchored_clause23454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom3573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05148
  ] at hbad
  tauto

theorem fin15Anchored_clause23455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom3573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05148
  ] at hbad
  tauto

theorem fin15Anchored_clause23456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom3573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05148
  ] at hbad
  tauto

theorem fin15Anchored_clause23457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom3573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05148
  ] at hbad
  tauto

theorem fin15Anchored_clause23458 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom1113 Fin15AnchoredAtom1152
    Fin15AnchoredAtom1197 Fin15AnchoredAtom1362 Fin15AnchoredAtom3573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05148
  ] at hbad
  tauto

theorem fin15Anchored_clause23459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom3574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09244
  ] at hbad
  tauto

theorem fin15Anchored_clause23460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom3574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09244
  ] at hbad
  tauto

theorem fin15Anchored_clause23461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom3574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09244
  ] at hbad
  tauto

theorem fin15Anchored_clause23462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom3574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09244
  ] at hbad
  tauto

theorem fin15Anchored_clause23463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom3574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09244
  ] at hbad
  tauto

theorem fin15Anchored_clause23464 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom1114 Fin15AnchoredAtom1153
    Fin15AnchoredAtom1198 Fin15AnchoredAtom1363 Fin15AnchoredAtom3574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09244
  ] at hbad
  tauto

theorem fin15Anchored_clause23465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom3575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17436
  ] at hbad
  tauto

theorem fin15Anchored_clause23466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom3575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17436
  ] at hbad
  tauto

theorem fin15Anchored_clause23467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1154 Fin15AnchoredAtom3575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17436
  ] at hbad
  tauto

theorem fin15Anchored_clause23468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom3575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17436
  ] at hbad
  tauto

theorem fin15Anchored_clause23469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom3575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17436
  ] at hbad
  tauto

theorem fin15Anchored_clause23470 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom1111 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1111 Fin15AnchoredAtom1115 Fin15AnchoredAtom1154
    Fin15AnchoredAtom1199 Fin15AnchoredAtom1364 Fin15AnchoredAtom3575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17436
  ] at hbad
  tauto

theorem fin15Anchored_clause23471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3576 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom3576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06172
  ] at hbad
  tauto

theorem fin15Anchored_clause23472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3577 chi ∧
      ¬Fin15AnchoredAtom1112 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1112 Fin15AnchoredAtom3577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10268
  ] at hbad
  tauto

theorem fin15Anchored_clause23473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3577 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom3577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10268
  ] at hbad
  tauto

theorem fin15Anchored_clause23474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3578 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom3578 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18460
  ] at hbad
  tauto

theorem fin15Anchored_clause23475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom3579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12316
  ] at hbad
  tauto

theorem fin15Anchored_clause23476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom3579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12316
  ] at hbad
  tauto

theorem fin15Anchored_clause23477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom3579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12316
  ] at hbad
  tauto

theorem fin15Anchored_clause23478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom3579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12316
  ] at hbad
  tauto

theorem fin15Anchored_clause23479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom3579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12316
  ] at hbad
  tauto

theorem fin15Anchored_clause23480 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom1114 Fin15AnchoredAtom1158
    Fin15AnchoredAtom1203 Fin15AnchoredAtom1368 Fin15AnchoredAtom3579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12316
  ] at hbad
  tauto

theorem fin15Anchored_clause23481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom3580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20508
  ] at hbad
  tauto

theorem fin15Anchored_clause23482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom3580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20508
  ] at hbad
  tauto

theorem fin15Anchored_clause23483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1159 Fin15AnchoredAtom3580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20508
  ] at hbad
  tauto

theorem fin15Anchored_clause23484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom3580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20508
  ] at hbad
  tauto

theorem fin15Anchored_clause23485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom3580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20508
  ] at hbad
  tauto

theorem fin15Anchored_clause23486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom1113 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom1115 Fin15AnchoredAtom1159
    Fin15AnchoredAtom1204 Fin15AnchoredAtom1369 Fin15AnchoredAtom3580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20508
  ] at hbad
  tauto

theorem fin15Anchored_clause23487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom3581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24604
  ] at hbad
  tauto

theorem fin15Anchored_clause23488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom3581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24604
  ] at hbad
  tauto

theorem fin15Anchored_clause23489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1160 Fin15AnchoredAtom3581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24604
  ] at hbad
  tauto

theorem fin15Anchored_clause23490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1205 Fin15AnchoredAtom3581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24604
  ] at hbad
  tauto

theorem fin15Anchored_clause23491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom3581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24604
  ] at hbad
  tauto

theorem fin15Anchored_clause23492 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom1114 chi ∧
      Fin15AnchoredAtom1115 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom1115 Fin15AnchoredAtom1160
    Fin15AnchoredAtom1205 Fin15AnchoredAtom1370 Fin15AnchoredAtom3581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24604
  ] at hbad
  tauto

theorem fin15Anchored_clause23493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom3582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00236
  ] at hbad
  tauto

theorem fin15Anchored_clause23494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom3582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00236
  ] at hbad
  tauto

theorem fin15Anchored_clause23495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom3582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00236
  ] at hbad
  tauto

theorem fin15Anchored_clause23496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom3582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00236
  ] at hbad
  tauto

theorem fin15Anchored_clause23497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom3582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00236
  ] at hbad
  tauto

theorem fin15Anchored_clause23498 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom1117 Fin15AnchoredAtom1125
    Fin15AnchoredAtom1206 Fin15AnchoredAtom1371 Fin15AnchoredAtom3582 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00236
  ] at hbad
  tauto

theorem fin15Anchored_clause23499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3583 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom3583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00364
  ] at hbad
  tauto

theorem fin15Anchored_clause23500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom3584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00620
  ] at hbad
  tauto

theorem fin15Anchored_clause23501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom3584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00620
  ] at hbad
  tauto

theorem fin15Anchored_clause23502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom3584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00620
  ] at hbad
  tauto

theorem fin15Anchored_clause23503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom3584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00620
  ] at hbad
  tauto

theorem fin15Anchored_clause23504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom3584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00620
  ] at hbad
  tauto

theorem fin15Anchored_clause23505 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom1119 Fin15AnchoredAtom1127
    Fin15AnchoredAtom1208 Fin15AnchoredAtom1373 Fin15AnchoredAtom3584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00620
  ] at hbad
  tauto

theorem fin15Anchored_clause23506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom3585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01132
  ] at hbad
  tauto

theorem fin15Anchored_clause23507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom3585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01132
  ] at hbad
  tauto

theorem fin15Anchored_clause23508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom3585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01132
  ] at hbad
  tauto

theorem fin15Anchored_clause23509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom3585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01132
  ] at hbad
  tauto

theorem fin15Anchored_clause23510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom3585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01132
  ] at hbad
  tauto

theorem fin15Anchored_clause23511 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom1120 Fin15AnchoredAtom1128
    Fin15AnchoredAtom1209 Fin15AnchoredAtom1374 Fin15AnchoredAtom3585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01132
  ] at hbad
  tauto

theorem fin15Anchored_clause23512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3586 chi ∧
      ¬Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1375 Fin15AnchoredAtom3586 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02156
  ] at hbad
  tauto

theorem fin15Anchored_clause23513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom3587 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04204
  ] at hbad
  tauto

theorem fin15Anchored_clause23514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom3587 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04204
  ] at hbad
  tauto

theorem fin15Anchored_clause23515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom3587 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04204
  ] at hbad
  tauto

theorem fin15Anchored_clause23516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom3587 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04204
  ] at hbad
  tauto

theorem fin15Anchored_clause23517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom3587 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04204
  ] at hbad
  tauto

theorem fin15Anchored_clause23518 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom1122 Fin15AnchoredAtom1130
    Fin15AnchoredAtom1211 Fin15AnchoredAtom1376 Fin15AnchoredAtom3587 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04204
  ] at hbad
  tauto

theorem fin15Anchored_clause23519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom3588 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08300
  ] at hbad
  tauto

theorem fin15Anchored_clause23520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom3588 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08300
  ] at hbad
  tauto

theorem fin15Anchored_clause23521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom3588 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08300
  ] at hbad
  tauto

theorem fin15Anchored_clause23522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom3588 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08300
  ] at hbad
  tauto

theorem fin15Anchored_clause23523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom3588 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08300
  ] at hbad
  tauto

theorem fin15Anchored_clause23524 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom1123 Fin15AnchoredAtom1131
    Fin15AnchoredAtom1212 Fin15AnchoredAtom1377 Fin15AnchoredAtom3588 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08300
  ] at hbad
  tauto

theorem fin15Anchored_clause23525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom3589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16492
  ] at hbad
  tauto

theorem fin15Anchored_clause23526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1124 Fin15AnchoredAtom3589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16492
  ] at hbad
  tauto

theorem fin15Anchored_clause23527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom3589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16492
  ] at hbad
  tauto

theorem fin15Anchored_clause23528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom3589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16492
  ] at hbad
  tauto

theorem fin15Anchored_clause23529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom3589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16492
  ] at hbad
  tauto

theorem fin15Anchored_clause23530 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom1116 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom1124 Fin15AnchoredAtom1132
    Fin15AnchoredAtom1213 Fin15AnchoredAtom1378 Fin15AnchoredAtom3589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16492
  ] at hbad
  tauto

theorem fin15Anchored_clause23531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3590 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom3590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00428
  ] at hbad
  tauto

theorem fin15Anchored_clause23532 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3590 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1118 chi ∧
      Fin15AnchoredAtom1133 chi ∧
      Fin15AnchoredAtom1214 chi ∧
      Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom1118 Fin15AnchoredAtom1133
    Fin15AnchoredAtom1214 Fin15AnchoredAtom1379 Fin15AnchoredAtom3590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00428
  ] at hbad
  tauto

theorem fin15Anchored_clause23533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom3591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00684
  ] at hbad
  tauto

theorem fin15Anchored_clause23534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom3591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00684
  ] at hbad
  tauto

theorem fin15Anchored_clause23535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom3591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00684
  ] at hbad
  tauto

theorem fin15Anchored_clause23536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom3591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00684
  ] at hbad
  tauto

theorem fin15Anchored_clause23537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom3591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00684
  ] at hbad
  tauto

theorem fin15Anchored_clause23538 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom1119 Fin15AnchoredAtom1134
    Fin15AnchoredAtom1215 Fin15AnchoredAtom1380 Fin15AnchoredAtom3591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00684
  ] at hbad
  tauto

theorem fin15Anchored_clause23539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom3592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01196
  ] at hbad
  tauto

theorem fin15Anchored_clause23540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom3592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01196
  ] at hbad
  tauto

theorem fin15Anchored_clause23541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom3592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01196
  ] at hbad
  tauto

theorem fin15Anchored_clause23542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom3592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01196
  ] at hbad
  tauto

theorem fin15Anchored_clause23543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom3592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01196
  ] at hbad
  tauto

theorem fin15Anchored_clause23544 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom1120 Fin15AnchoredAtom1135
    Fin15AnchoredAtom1216 Fin15AnchoredAtom1381 Fin15AnchoredAtom3592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01196
  ] at hbad
  tauto

theorem fin15Anchored_clause23545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3593 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom3593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02220
  ] at hbad
  tauto

theorem fin15Anchored_clause23546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3593 chi ∧
      ¬Fin15AnchoredAtom1382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1382 Fin15AnchoredAtom3593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02220
  ] at hbad
  tauto

theorem fin15Anchored_clause23547 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3593 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1121 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1217 chi ∧
      Fin15AnchoredAtom1382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom1121 Fin15AnchoredAtom1136
    Fin15AnchoredAtom1217 Fin15AnchoredAtom1382 Fin15AnchoredAtom3593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02220
  ] at hbad
  tauto

theorem fin15Anchored_clause23548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom3594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04268
  ] at hbad
  tauto

theorem fin15Anchored_clause23549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom3594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04268
  ] at hbad
  tauto

theorem fin15Anchored_clause23550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom3594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04268
  ] at hbad
  tauto

theorem fin15Anchored_clause23551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom3594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04268
  ] at hbad
  tauto

end ErdosSzekeres

end
