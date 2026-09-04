module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 200. -/

theorem fin15Anchored_clause25600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom4162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04456
  ] at hbad
  tauto

theorem fin15Anchored_clause25601 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4162 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom1376 Fin15AnchoredAtom1389
    Fin15AnchoredAtom1417 Fin15AnchoredAtom1621 Fin15AnchoredAtom4162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04456
  ] at hbad
  tauto

theorem fin15Anchored_clause25602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom4163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08552
  ] at hbad
  tauto

theorem fin15Anchored_clause25603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom4163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08552
  ] at hbad
  tauto

theorem fin15Anchored_clause25604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom4163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08552
  ] at hbad
  tauto

theorem fin15Anchored_clause25605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom4163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08552
  ] at hbad
  tauto

theorem fin15Anchored_clause25606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4163 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom4163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08552
  ] at hbad
  tauto

theorem fin15Anchored_clause25607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4163 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom1377 Fin15AnchoredAtom1390
    Fin15AnchoredAtom1418 Fin15AnchoredAtom1622 Fin15AnchoredAtom4163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08552
  ] at hbad
  tauto

theorem fin15Anchored_clause25608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom4164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16744
  ] at hbad
  tauto

theorem fin15Anchored_clause25609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom4164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16744
  ] at hbad
  tauto

theorem fin15Anchored_clause25610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1391 Fin15AnchoredAtom4164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16744
  ] at hbad
  tauto

theorem fin15Anchored_clause25611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1419 Fin15AnchoredAtom4164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16744
  ] at hbad
  tauto

theorem fin15Anchored_clause25612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4164 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1623 Fin15AnchoredAtom4164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16744
  ] at hbad
  tauto

theorem fin15Anchored_clause25613 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4164 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom1378 Fin15AnchoredAtom1391
    Fin15AnchoredAtom1419 Fin15AnchoredAtom1623 Fin15AnchoredAtom4164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16744
  ] at hbad
  tauto

theorem fin15Anchored_clause25614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom4165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01640
  ] at hbad
  tauto

theorem fin15Anchored_clause25615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom4165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01640
  ] at hbad
  tauto

theorem fin15Anchored_clause25616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom4165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01640
  ] at hbad
  tauto

theorem fin15Anchored_clause25617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom4165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01640
  ] at hbad
  tauto

theorem fin15Anchored_clause25618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4165 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom4165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01640
  ] at hbad
  tauto

theorem fin15Anchored_clause25619 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom1374 Fin15AnchoredAtom1392
    Fin15AnchoredAtom1420 Fin15AnchoredAtom1624 Fin15AnchoredAtom4165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01640
  ] at hbad
  tauto

theorem fin15Anchored_clause25620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4166 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom4166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02664
  ] at hbad
  tauto

theorem fin15Anchored_clause25621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4166 chi ∧
      ¬Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1375 Fin15AnchoredAtom4166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02664
  ] at hbad
  tauto

theorem fin15Anchored_clause25622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom4167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04712
  ] at hbad
  tauto

theorem fin15Anchored_clause25623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom4167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04712
  ] at hbad
  tauto

theorem fin15Anchored_clause25624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom4167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04712
  ] at hbad
  tauto

theorem fin15Anchored_clause25625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom4167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04712
  ] at hbad
  tauto

theorem fin15Anchored_clause25626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4167 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom4167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04712
  ] at hbad
  tauto

theorem fin15Anchored_clause25627 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom1376 Fin15AnchoredAtom1394
    Fin15AnchoredAtom1422 Fin15AnchoredAtom1626 Fin15AnchoredAtom4167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04712
  ] at hbad
  tauto

theorem fin15Anchored_clause25628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom4168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08808
  ] at hbad
  tauto

theorem fin15Anchored_clause25629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom4168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08808
  ] at hbad
  tauto

theorem fin15Anchored_clause25630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom4168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08808
  ] at hbad
  tauto

theorem fin15Anchored_clause25631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom4168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08808
  ] at hbad
  tauto

theorem fin15Anchored_clause25632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4168 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom4168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08808
  ] at hbad
  tauto

theorem fin15Anchored_clause25633 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom1377 Fin15AnchoredAtom1395
    Fin15AnchoredAtom1423 Fin15AnchoredAtom1627 Fin15AnchoredAtom4168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08808
  ] at hbad
  tauto

theorem fin15Anchored_clause25634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom4169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17000
  ] at hbad
  tauto

theorem fin15Anchored_clause25635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom4169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17000
  ] at hbad
  tauto

theorem fin15Anchored_clause25636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom4169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17000
  ] at hbad
  tauto

theorem fin15Anchored_clause25637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom4169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17000
  ] at hbad
  tauto

theorem fin15Anchored_clause25638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4169 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom4169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17000
  ] at hbad
  tauto

theorem fin15Anchored_clause25639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom1378 Fin15AnchoredAtom1396
    Fin15AnchoredAtom1424 Fin15AnchoredAtom1628 Fin15AnchoredAtom4169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17000
  ] at hbad
  tauto

theorem fin15Anchored_clause25640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4170 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom4170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03176
  ] at hbad
  tauto

theorem fin15Anchored_clause25641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4170 chi ∧
      ¬Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1425 Fin15AnchoredAtom4170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03176
  ] at hbad
  tauto

theorem fin15Anchored_clause25642 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4170 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1375 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom1375 Fin15AnchoredAtom1397
    Fin15AnchoredAtom1425 Fin15AnchoredAtom1629 Fin15AnchoredAtom4170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03176
  ] at hbad
  tauto

theorem fin15Anchored_clause25643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom4171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05224
  ] at hbad
  tauto

theorem fin15Anchored_clause25644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom4171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05224
  ] at hbad
  tauto

theorem fin15Anchored_clause25645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom4171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05224
  ] at hbad
  tauto

theorem fin15Anchored_clause25646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom4171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05224
  ] at hbad
  tauto

theorem fin15Anchored_clause25647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4171 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom4171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05224
  ] at hbad
  tauto

theorem fin15Anchored_clause25648 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom1376 Fin15AnchoredAtom1398
    Fin15AnchoredAtom1426 Fin15AnchoredAtom1630 Fin15AnchoredAtom4171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05224
  ] at hbad
  tauto

theorem fin15Anchored_clause25649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom4172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09320
  ] at hbad
  tauto

theorem fin15Anchored_clause25650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom4172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09320
  ] at hbad
  tauto

theorem fin15Anchored_clause25651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom4172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09320
  ] at hbad
  tauto

theorem fin15Anchored_clause25652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom4172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09320
  ] at hbad
  tauto

theorem fin15Anchored_clause25653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4172 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom4172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09320
  ] at hbad
  tauto

theorem fin15Anchored_clause25654 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom1377 Fin15AnchoredAtom1399
    Fin15AnchoredAtom1427 Fin15AnchoredAtom1631 Fin15AnchoredAtom4172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09320
  ] at hbad
  tauto

theorem fin15Anchored_clause25655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom4173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17512
  ] at hbad
  tauto

theorem fin15Anchored_clause25656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom4173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17512
  ] at hbad
  tauto

theorem fin15Anchored_clause25657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom4173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17512
  ] at hbad
  tauto

theorem fin15Anchored_clause25658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom4173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17512
  ] at hbad
  tauto

theorem fin15Anchored_clause25659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4173 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom4173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17512
  ] at hbad
  tauto

theorem fin15Anchored_clause25660 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom1378 Fin15AnchoredAtom1400
    Fin15AnchoredAtom1428 Fin15AnchoredAtom1632 Fin15AnchoredAtom4173 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17512
  ] at hbad
  tauto

theorem fin15Anchored_clause25661 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4174 chi ∧
      Fin15AnchoredAtom1375 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1401 chi ∧
      Fin15AnchoredAtom1429 chi ∧
      Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1375 Fin15AnchoredAtom1376 Fin15AnchoredAtom1401
    Fin15AnchoredAtom1429 Fin15AnchoredAtom1633 Fin15AnchoredAtom4174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06248
  ] at hbad
  tauto

theorem fin15Anchored_clause25662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4176 chi ∧
      ¬Fin15AnchoredAtom1375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1375 Fin15AnchoredAtom4176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18536
  ] at hbad
  tauto

theorem fin15Anchored_clause25663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom4177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12392
  ] at hbad
  tauto

theorem fin15Anchored_clause25664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom4177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12392
  ] at hbad
  tauto

theorem fin15Anchored_clause25665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom4177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12392
  ] at hbad
  tauto

theorem fin15Anchored_clause25666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom4177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12392
  ] at hbad
  tauto

theorem fin15Anchored_clause25667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4177 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom4177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12392
  ] at hbad
  tauto

theorem fin15Anchored_clause25668 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom1377 Fin15AnchoredAtom1404
    Fin15AnchoredAtom1432 Fin15AnchoredAtom1636 Fin15AnchoredAtom4177 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12392
  ] at hbad
  tauto

theorem fin15Anchored_clause25669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom4178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20584
  ] at hbad
  tauto

theorem fin15Anchored_clause25670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom4178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20584
  ] at hbad
  tauto

theorem fin15Anchored_clause25671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom4178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20584
  ] at hbad
  tauto

theorem fin15Anchored_clause25672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom4178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20584
  ] at hbad
  tauto

theorem fin15Anchored_clause25673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4178 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom4178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20584
  ] at hbad
  tauto

theorem fin15Anchored_clause25674 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom1378 Fin15AnchoredAtom1405
    Fin15AnchoredAtom1433 Fin15AnchoredAtom1637 Fin15AnchoredAtom4178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20584
  ] at hbad
  tauto

theorem fin15Anchored_clause25675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom4179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24680
  ] at hbad
  tauto

theorem fin15Anchored_clause25676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom4179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24680
  ] at hbad
  tauto

theorem fin15Anchored_clause25677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom4179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24680
  ] at hbad
  tauto

theorem fin15Anchored_clause25678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom4179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24680
  ] at hbad
  tauto

theorem fin15Anchored_clause25679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4179 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom4179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24680
  ] at hbad
  tauto

theorem fin15Anchored_clause25680 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom1378 Fin15AnchoredAtom1406
    Fin15AnchoredAtom1434 Fin15AnchoredAtom1638 Fin15AnchoredAtom4179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24680
  ] at hbad
  tauto

theorem fin15Anchored_clause25681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom4180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00936
  ] at hbad
  tauto

theorem fin15Anchored_clause25682 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom4180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00936
  ] at hbad
  tauto

theorem fin15Anchored_clause25683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom4180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00936
  ] at hbad
  tauto

theorem fin15Anchored_clause25684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom4180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00936
  ] at hbad
  tauto

theorem fin15Anchored_clause25685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4180 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom4180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00936
  ] at hbad
  tauto

theorem fin15Anchored_clause25686 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4180 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom1380 Fin15AnchoredAtom1386
    Fin15AnchoredAtom1435 Fin15AnchoredAtom1639 Fin15AnchoredAtom4180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00936
  ] at hbad
  tauto

theorem fin15Anchored_clause25687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom4181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01448
  ] at hbad
  tauto

theorem fin15Anchored_clause25688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom4181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01448
  ] at hbad
  tauto

theorem fin15Anchored_clause25689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom4181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01448
  ] at hbad
  tauto

theorem fin15Anchored_clause25690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom4181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01448
  ] at hbad
  tauto

theorem fin15Anchored_clause25691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4181 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom4181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01448
  ] at hbad
  tauto

theorem fin15Anchored_clause25692 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4181 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom1381 Fin15AnchoredAtom1387
    Fin15AnchoredAtom1436 Fin15AnchoredAtom1640 Fin15AnchoredAtom4181 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01448
  ] at hbad
  tauto

theorem fin15Anchored_clause25693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom4183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04520
  ] at hbad
  tauto

theorem fin15Anchored_clause25694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom4183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04520
  ] at hbad
  tauto

theorem fin15Anchored_clause25695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom4183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04520
  ] at hbad
  tauto

theorem fin15Anchored_clause25696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom4183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04520
  ] at hbad
  tauto

theorem fin15Anchored_clause25697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4183 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom4183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04520
  ] at hbad
  tauto

theorem fin15Anchored_clause25698 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4183 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom1383 Fin15AnchoredAtom1389
    Fin15AnchoredAtom1438 Fin15AnchoredAtom1642 Fin15AnchoredAtom4183 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04520
  ] at hbad
  tauto

theorem fin15Anchored_clause25699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom4184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08616
  ] at hbad
  tauto

theorem fin15Anchored_clause25700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom4184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08616
  ] at hbad
  tauto

theorem fin15Anchored_clause25701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom4184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08616
  ] at hbad
  tauto

theorem fin15Anchored_clause25702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1439 Fin15AnchoredAtom4184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08616
  ] at hbad
  tauto

theorem fin15Anchored_clause25703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4184 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom4184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08616
  ] at hbad
  tauto

theorem fin15Anchored_clause25704 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4184 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom1384 Fin15AnchoredAtom1390
    Fin15AnchoredAtom1439 Fin15AnchoredAtom1643 Fin15AnchoredAtom4184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08616
  ] at hbad
  tauto

theorem fin15Anchored_clause25705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom4185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16808
  ] at hbad
  tauto

theorem fin15Anchored_clause25706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom4185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16808
  ] at hbad
  tauto

theorem fin15Anchored_clause25707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1391 Fin15AnchoredAtom4185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16808
  ] at hbad
  tauto

theorem fin15Anchored_clause25708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1440 Fin15AnchoredAtom4185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16808
  ] at hbad
  tauto

theorem fin15Anchored_clause25709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4185 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1644 Fin15AnchoredAtom4185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16808
  ] at hbad
  tauto

theorem fin15Anchored_clause25710 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4185 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom1385 Fin15AnchoredAtom1391
    Fin15AnchoredAtom1440 Fin15AnchoredAtom1644 Fin15AnchoredAtom4185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16808
  ] at hbad
  tauto

theorem fin15Anchored_clause25711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom4186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01704
  ] at hbad
  tauto

theorem fin15Anchored_clause25712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom4186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01704
  ] at hbad
  tauto

theorem fin15Anchored_clause25713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom4186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01704
  ] at hbad
  tauto

theorem fin15Anchored_clause25714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom4186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01704
  ] at hbad
  tauto

theorem fin15Anchored_clause25715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4186 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom4186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01704
  ] at hbad
  tauto

theorem fin15Anchored_clause25716 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom1381 Fin15AnchoredAtom1392
    Fin15AnchoredAtom1441 Fin15AnchoredAtom1645 Fin15AnchoredAtom4186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01704
  ] at hbad
  tauto

theorem fin15Anchored_clause25717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4187 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom4187 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02728
  ] at hbad
  tauto

theorem fin15Anchored_clause25718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4187 chi ∧
      ¬Fin15AnchoredAtom1382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1382 Fin15AnchoredAtom4187 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02728
  ] at hbad
  tauto

theorem fin15Anchored_clause25719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4187 chi ∧
      ¬Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1442 Fin15AnchoredAtom4187 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02728
  ] at hbad
  tauto

theorem fin15Anchored_clause25720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom4188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04776
  ] at hbad
  tauto

theorem fin15Anchored_clause25721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom4188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04776
  ] at hbad
  tauto

theorem fin15Anchored_clause25722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom4188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04776
  ] at hbad
  tauto

theorem fin15Anchored_clause25723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom4188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04776
  ] at hbad
  tauto

theorem fin15Anchored_clause25724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4188 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom4188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04776
  ] at hbad
  tauto

theorem fin15Anchored_clause25725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom1383 Fin15AnchoredAtom1394
    Fin15AnchoredAtom1443 Fin15AnchoredAtom1647 Fin15AnchoredAtom4188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04776
  ] at hbad
  tauto

theorem fin15Anchored_clause25726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom4189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08872
  ] at hbad
  tauto

theorem fin15Anchored_clause25727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom4189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08872
  ] at hbad
  tauto

end ErdosSzekeres

end
