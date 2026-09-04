module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 198. -/

theorem fin15Anchored_clause25344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom4102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01688
  ] at hbad
  tauto

theorem fin15Anchored_clause25345 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom4102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01688
  ] at hbad
  tauto

theorem fin15Anchored_clause25346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom4102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01688
  ] at hbad
  tauto

theorem fin15Anchored_clause25347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom4102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01688
  ] at hbad
  tauto

theorem fin15Anchored_clause25348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4102 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom4102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01688
  ] at hbad
  tauto

theorem fin15Anchored_clause25349 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom1345 Fin15AnchoredAtom1356
    Fin15AnchoredAtom1441 Fin15AnchoredAtom1561 Fin15AnchoredAtom4102 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01688
  ] at hbad
  tauto

theorem fin15Anchored_clause25350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4103 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom4103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02712
  ] at hbad
  tauto

theorem fin15Anchored_clause25351 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4103 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1562 Fin15AnchoredAtom4103 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02712
  ] at hbad
  tauto

theorem fin15Anchored_clause25352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom4104 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04760
  ] at hbad
  tauto

theorem fin15Anchored_clause25353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom4104 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04760
  ] at hbad
  tauto

theorem fin15Anchored_clause25354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom4104 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04760
  ] at hbad
  tauto

theorem fin15Anchored_clause25355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom4104 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04760
  ] at hbad
  tauto

theorem fin15Anchored_clause25356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4104 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom4104 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04760
  ] at hbad
  tauto

theorem fin15Anchored_clause25357 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom1347 Fin15AnchoredAtom1358
    Fin15AnchoredAtom1443 Fin15AnchoredAtom1563 Fin15AnchoredAtom4104 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04760
  ] at hbad
  tauto

theorem fin15Anchored_clause25358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom4105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08856
  ] at hbad
  tauto

theorem fin15Anchored_clause25359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom4105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08856
  ] at hbad
  tauto

theorem fin15Anchored_clause25360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom4105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08856
  ] at hbad
  tauto

theorem fin15Anchored_clause25361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom4105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08856
  ] at hbad
  tauto

theorem fin15Anchored_clause25362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4105 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom4105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08856
  ] at hbad
  tauto

theorem fin15Anchored_clause25363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom1348 Fin15AnchoredAtom1359
    Fin15AnchoredAtom1444 Fin15AnchoredAtom1564 Fin15AnchoredAtom4105 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08856
  ] at hbad
  tauto

theorem fin15Anchored_clause25364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom4106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17048
  ] at hbad
  tauto

theorem fin15Anchored_clause25365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom4106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17048
  ] at hbad
  tauto

theorem fin15Anchored_clause25366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom4106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17048
  ] at hbad
  tauto

theorem fin15Anchored_clause25367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom4106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17048
  ] at hbad
  tauto

theorem fin15Anchored_clause25368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4106 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom4106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17048
  ] at hbad
  tauto

theorem fin15Anchored_clause25369 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom1349 Fin15AnchoredAtom1360
    Fin15AnchoredAtom1445 Fin15AnchoredAtom1565 Fin15AnchoredAtom4106 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17048
  ] at hbad
  tauto

theorem fin15Anchored_clause25370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4107 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom4107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03224
  ] at hbad
  tauto

theorem fin15Anchored_clause25371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4107 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1566 Fin15AnchoredAtom4107 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03224
  ] at hbad
  tauto

theorem fin15Anchored_clause25372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom4108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05272
  ] at hbad
  tauto

theorem fin15Anchored_clause25373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom4108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05272
  ] at hbad
  tauto

theorem fin15Anchored_clause25374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom4108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05272
  ] at hbad
  tauto

theorem fin15Anchored_clause25375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom4108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05272
  ] at hbad
  tauto

theorem fin15Anchored_clause25376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4108 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom4108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05272
  ] at hbad
  tauto

theorem fin15Anchored_clause25377 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom1347 Fin15AnchoredAtom1362
    Fin15AnchoredAtom1447 Fin15AnchoredAtom1567 Fin15AnchoredAtom4108 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05272
  ] at hbad
  tauto

theorem fin15Anchored_clause25378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom4109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09368
  ] at hbad
  tauto

theorem fin15Anchored_clause25379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom4109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09368
  ] at hbad
  tauto

theorem fin15Anchored_clause25380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom4109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09368
  ] at hbad
  tauto

theorem fin15Anchored_clause25381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom4109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09368
  ] at hbad
  tauto

theorem fin15Anchored_clause25382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4109 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom4109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09368
  ] at hbad
  tauto

theorem fin15Anchored_clause25383 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom1348 Fin15AnchoredAtom1363
    Fin15AnchoredAtom1448 Fin15AnchoredAtom1568 Fin15AnchoredAtom4109 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09368
  ] at hbad
  tauto

theorem fin15Anchored_clause25384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom4110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17560
  ] at hbad
  tauto

theorem fin15Anchored_clause25385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom4110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17560
  ] at hbad
  tauto

theorem fin15Anchored_clause25386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom4110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17560
  ] at hbad
  tauto

theorem fin15Anchored_clause25387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom4110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17560
  ] at hbad
  tauto

theorem fin15Anchored_clause25388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4110 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom4110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17560
  ] at hbad
  tauto

theorem fin15Anchored_clause25389 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom1349 Fin15AnchoredAtom1364
    Fin15AnchoredAtom1449 Fin15AnchoredAtom1569 Fin15AnchoredAtom4110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17560
  ] at hbad
  tauto

theorem fin15Anchored_clause25390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4111 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom4111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06296
  ] at hbad
  tauto

theorem fin15Anchored_clause25391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4111 chi ∧
      ¬Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1570 Fin15AnchoredAtom4111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06296
  ] at hbad
  tauto

theorem fin15Anchored_clause25392 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4111 chi ∧
      Fin15AnchoredAtom1346 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1365 chi ∧
      Fin15AnchoredAtom1450 chi ∧
      Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1346 Fin15AnchoredAtom1347 Fin15AnchoredAtom1365
    Fin15AnchoredAtom1450 Fin15AnchoredAtom1570 Fin15AnchoredAtom4111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06296
  ] at hbad
  tauto

theorem fin15Anchored_clause25393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom4114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12440
  ] at hbad
  tauto

theorem fin15Anchored_clause25394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom4114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12440
  ] at hbad
  tauto

theorem fin15Anchored_clause25395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom4114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12440
  ] at hbad
  tauto

theorem fin15Anchored_clause25396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom4114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12440
  ] at hbad
  tauto

theorem fin15Anchored_clause25397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4114 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom4114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12440
  ] at hbad
  tauto

theorem fin15Anchored_clause25398 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom1348 Fin15AnchoredAtom1368
    Fin15AnchoredAtom1453 Fin15AnchoredAtom1573 Fin15AnchoredAtom4114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12440
  ] at hbad
  tauto

theorem fin15Anchored_clause25399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom4115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20632
  ] at hbad
  tauto

theorem fin15Anchored_clause25400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom4115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20632
  ] at hbad
  tauto

theorem fin15Anchored_clause25401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom4115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20632
  ] at hbad
  tauto

theorem fin15Anchored_clause25402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom4115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20632
  ] at hbad
  tauto

theorem fin15Anchored_clause25403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4115 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom4115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20632
  ] at hbad
  tauto

theorem fin15Anchored_clause25404 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom1349 Fin15AnchoredAtom1369
    Fin15AnchoredAtom1454 Fin15AnchoredAtom1574 Fin15AnchoredAtom4115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20632
  ] at hbad
  tauto

theorem fin15Anchored_clause25405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom4116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24728
  ] at hbad
  tauto

theorem fin15Anchored_clause25406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom4116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24728
  ] at hbad
  tauto

theorem fin15Anchored_clause25407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom4116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24728
  ] at hbad
  tauto

theorem fin15Anchored_clause25408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom4116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24728
  ] at hbad
  tauto

theorem fin15Anchored_clause25409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4116 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom4116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24728
  ] at hbad
  tauto

theorem fin15Anchored_clause25410 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom1349 Fin15AnchoredAtom1370
    Fin15AnchoredAtom1455 Fin15AnchoredAtom1575 Fin15AnchoredAtom4116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24728
  ] at hbad
  tauto

theorem fin15Anchored_clause25411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom4117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01816
  ] at hbad
  tauto

theorem fin15Anchored_clause25412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom4117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01816
  ] at hbad
  tauto

theorem fin15Anchored_clause25413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom4117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01816
  ] at hbad
  tauto

theorem fin15Anchored_clause25414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom4117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01816
  ] at hbad
  tauto

theorem fin15Anchored_clause25415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4117 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom4117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01816
  ] at hbad
  tauto

theorem fin15Anchored_clause25416 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom1351 Fin15AnchoredAtom1356
    Fin15AnchoredAtom1456 Fin15AnchoredAtom1576 Fin15AnchoredAtom4117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01816
  ] at hbad
  tauto

theorem fin15Anchored_clause25417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom4119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04888
  ] at hbad
  tauto

theorem fin15Anchored_clause25418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom4119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04888
  ] at hbad
  tauto

theorem fin15Anchored_clause25419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom4119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04888
  ] at hbad
  tauto

theorem fin15Anchored_clause25420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom4119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04888
  ] at hbad
  tauto

theorem fin15Anchored_clause25421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4119 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom4119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04888
  ] at hbad
  tauto

theorem fin15Anchored_clause25422 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4119 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom1353 Fin15AnchoredAtom1358
    Fin15AnchoredAtom1458 Fin15AnchoredAtom1578 Fin15AnchoredAtom4119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04888
  ] at hbad
  tauto

theorem fin15Anchored_clause25423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom4120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08984
  ] at hbad
  tauto

theorem fin15Anchored_clause25424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom4120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08984
  ] at hbad
  tauto

theorem fin15Anchored_clause25425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom4120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08984
  ] at hbad
  tauto

theorem fin15Anchored_clause25426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1459 Fin15AnchoredAtom4120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08984
  ] at hbad
  tauto

theorem fin15Anchored_clause25427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4120 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1579 Fin15AnchoredAtom4120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08984
  ] at hbad
  tauto

theorem fin15Anchored_clause25428 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4120 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom1354 Fin15AnchoredAtom1359
    Fin15AnchoredAtom1459 Fin15AnchoredAtom1579 Fin15AnchoredAtom4120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08984
  ] at hbad
  tauto

theorem fin15Anchored_clause25429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom4121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17176
  ] at hbad
  tauto

theorem fin15Anchored_clause25430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom4121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17176
  ] at hbad
  tauto

theorem fin15Anchored_clause25431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1460 Fin15AnchoredAtom4121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17176
  ] at hbad
  tauto

theorem fin15Anchored_clause25432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4121 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1580 Fin15AnchoredAtom4121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17176
  ] at hbad
  tauto

theorem fin15Anchored_clause25433 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4121 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom1355 Fin15AnchoredAtom1360
    Fin15AnchoredAtom1460 Fin15AnchoredAtom1580 Fin15AnchoredAtom4121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17176
  ] at hbad
  tauto

theorem fin15Anchored_clause25434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom4123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05400
  ] at hbad
  tauto

theorem fin15Anchored_clause25435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom4123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05400
  ] at hbad
  tauto

theorem fin15Anchored_clause25436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom4123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05400
  ] at hbad
  tauto

theorem fin15Anchored_clause25437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom4123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05400
  ] at hbad
  tauto

theorem fin15Anchored_clause25438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4123 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom4123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05400
  ] at hbad
  tauto

theorem fin15Anchored_clause25439 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4123 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom1353 Fin15AnchoredAtom1362
    Fin15AnchoredAtom1462 Fin15AnchoredAtom1582 Fin15AnchoredAtom4123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05400
  ] at hbad
  tauto

theorem fin15Anchored_clause25440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom4124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09496
  ] at hbad
  tauto

theorem fin15Anchored_clause25441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom4124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09496
  ] at hbad
  tauto

theorem fin15Anchored_clause25442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom4124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09496
  ] at hbad
  tauto

theorem fin15Anchored_clause25443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom4124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09496
  ] at hbad
  tauto

theorem fin15Anchored_clause25444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4124 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom4124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09496
  ] at hbad
  tauto

theorem fin15Anchored_clause25445 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom1354 Fin15AnchoredAtom1363
    Fin15AnchoredAtom1463 Fin15AnchoredAtom1583 Fin15AnchoredAtom4124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09496
  ] at hbad
  tauto

theorem fin15Anchored_clause25446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom4125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17688
  ] at hbad
  tauto

theorem fin15Anchored_clause25447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1355 Fin15AnchoredAtom4125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17688
  ] at hbad
  tauto

theorem fin15Anchored_clause25448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom4125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17688
  ] at hbad
  tauto

theorem fin15Anchored_clause25449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1464 Fin15AnchoredAtom4125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17688
  ] at hbad
  tauto

theorem fin15Anchored_clause25450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4125 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1584 Fin15AnchoredAtom4125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17688
  ] at hbad
  tauto

theorem fin15Anchored_clause25451 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4125 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom1355 Fin15AnchoredAtom1364
    Fin15AnchoredAtom1464 Fin15AnchoredAtom1584 Fin15AnchoredAtom4125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17688
  ] at hbad
  tauto

theorem fin15Anchored_clause25452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom4129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12568
  ] at hbad
  tauto

theorem fin15Anchored_clause25453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom4129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12568
  ] at hbad
  tauto

theorem fin15Anchored_clause25454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom4129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12568
  ] at hbad
  tauto

theorem fin15Anchored_clause25455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1468 Fin15AnchoredAtom4129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12568
  ] at hbad
  tauto

theorem fin15Anchored_clause25456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4129 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom4129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12568
  ] at hbad
  tauto

theorem fin15Anchored_clause25457 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4129 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom1354 Fin15AnchoredAtom1368
    Fin15AnchoredAtom1468 Fin15AnchoredAtom1588 Fin15AnchoredAtom4129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12568
  ] at hbad
  tauto

theorem fin15Anchored_clause25458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom4130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20760
  ] at hbad
  tauto

theorem fin15Anchored_clause25459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1355 Fin15AnchoredAtom4130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20760
  ] at hbad
  tauto

theorem fin15Anchored_clause25460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom4130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20760
  ] at hbad
  tauto

theorem fin15Anchored_clause25461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4130 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1589 Fin15AnchoredAtom4130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20760
  ] at hbad
  tauto

theorem fin15Anchored_clause25462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4130 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom1355 Fin15AnchoredAtom1369
    Fin15AnchoredAtom1469 Fin15AnchoredAtom1589 Fin15AnchoredAtom4130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20760
  ] at hbad
  tauto

theorem fin15Anchored_clause25463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom4131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24856
  ] at hbad
  tauto

theorem fin15Anchored_clause25464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1355 Fin15AnchoredAtom4131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24856
  ] at hbad
  tauto

theorem fin15Anchored_clause25465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom4131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24856
  ] at hbad
  tauto

theorem fin15Anchored_clause25466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1470 Fin15AnchoredAtom4131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24856
  ] at hbad
  tauto

theorem fin15Anchored_clause25467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4131 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom4131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24856
  ] at hbad
  tauto

theorem fin15Anchored_clause25468 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4131 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom1355 Fin15AnchoredAtom1370
    Fin15AnchoredAtom1470 Fin15AnchoredAtom1590 Fin15AnchoredAtom4131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24856
  ] at hbad
  tauto

theorem fin15Anchored_clause25469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4132 chi ∧
      ¬Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1471 Fin15AnchoredAtom4132 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03608
  ] at hbad
  tauto

theorem fin15Anchored_clause25470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4132 chi ∧
      ¬Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1591 Fin15AnchoredAtom4132 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03608
  ] at hbad
  tauto

theorem fin15Anchored_clause25471 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4132 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1357 chi ∧
      Fin15AnchoredAtom1361 chi ∧
      Fin15AnchoredAtom1471 chi ∧
      Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom1357 Fin15AnchoredAtom1361
    Fin15AnchoredAtom1471 Fin15AnchoredAtom1591 Fin15AnchoredAtom4132 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03608
  ] at hbad
  tauto

end ErdosSzekeres

end
