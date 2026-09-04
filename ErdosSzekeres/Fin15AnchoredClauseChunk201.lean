module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 201. -/

theorem fin15Anchored_clause25728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom4189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08872
  ] at hbad
  tauto

theorem fin15Anchored_clause25729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom4189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08872
  ] at hbad
  tauto

theorem fin15Anchored_clause25730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4189 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom4189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08872
  ] at hbad
  tauto

theorem fin15Anchored_clause25731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom1384 Fin15AnchoredAtom1395
    Fin15AnchoredAtom1444 Fin15AnchoredAtom1648 Fin15AnchoredAtom4189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08872
  ] at hbad
  tauto

theorem fin15Anchored_clause25732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom4190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17064
  ] at hbad
  tauto

theorem fin15Anchored_clause25733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom4190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17064
  ] at hbad
  tauto

theorem fin15Anchored_clause25734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom4190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17064
  ] at hbad
  tauto

theorem fin15Anchored_clause25735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom4190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17064
  ] at hbad
  tauto

theorem fin15Anchored_clause25736 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4190 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom4190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17064
  ] at hbad
  tauto

theorem fin15Anchored_clause25737 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom1385 Fin15AnchoredAtom1396
    Fin15AnchoredAtom1445 Fin15AnchoredAtom1649 Fin15AnchoredAtom4190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17064
  ] at hbad
  tauto

theorem fin15Anchored_clause25738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4191 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom4191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03240
  ] at hbad
  tauto

theorem fin15Anchored_clause25739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4191 chi ∧
      ¬Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1446 Fin15AnchoredAtom4191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03240
  ] at hbad
  tauto

theorem fin15Anchored_clause25740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4191 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom4191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03240
  ] at hbad
  tauto

theorem fin15Anchored_clause25741 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4191 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1382 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1446 chi ∧
      Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom1382 Fin15AnchoredAtom1397
    Fin15AnchoredAtom1446 Fin15AnchoredAtom1650 Fin15AnchoredAtom4191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03240
  ] at hbad
  tauto

theorem fin15Anchored_clause25742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom4192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05288
  ] at hbad
  tauto

theorem fin15Anchored_clause25743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom4192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05288
  ] at hbad
  tauto

theorem fin15Anchored_clause25744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom4192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05288
  ] at hbad
  tauto

theorem fin15Anchored_clause25745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom4192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05288
  ] at hbad
  tauto

theorem fin15Anchored_clause25746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4192 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom4192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05288
  ] at hbad
  tauto

theorem fin15Anchored_clause25747 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom1383 Fin15AnchoredAtom1398
    Fin15AnchoredAtom1447 Fin15AnchoredAtom1651 Fin15AnchoredAtom4192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05288
  ] at hbad
  tauto

theorem fin15Anchored_clause25748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom4193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09384
  ] at hbad
  tauto

theorem fin15Anchored_clause25749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom4193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09384
  ] at hbad
  tauto

theorem fin15Anchored_clause25750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom4193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09384
  ] at hbad
  tauto

theorem fin15Anchored_clause25751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom4193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09384
  ] at hbad
  tauto

theorem fin15Anchored_clause25752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4193 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom4193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09384
  ] at hbad
  tauto

theorem fin15Anchored_clause25753 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom1384 Fin15AnchoredAtom1399
    Fin15AnchoredAtom1448 Fin15AnchoredAtom1652 Fin15AnchoredAtom4193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09384
  ] at hbad
  tauto

theorem fin15Anchored_clause25754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom4194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17576
  ] at hbad
  tauto

theorem fin15Anchored_clause25755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom4194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17576
  ] at hbad
  tauto

theorem fin15Anchored_clause25756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom4194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17576
  ] at hbad
  tauto

theorem fin15Anchored_clause25757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom4194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17576
  ] at hbad
  tauto

theorem fin15Anchored_clause25758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4194 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom4194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17576
  ] at hbad
  tauto

theorem fin15Anchored_clause25759 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom1385 Fin15AnchoredAtom1400
    Fin15AnchoredAtom1449 Fin15AnchoredAtom1653 Fin15AnchoredAtom4194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17576
  ] at hbad
  tauto

theorem fin15Anchored_clause25760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom1382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1382 Fin15AnchoredAtom4195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06312
  ] at hbad
  tauto

theorem fin15Anchored_clause25761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom4195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06312
  ] at hbad
  tauto

theorem fin15Anchored_clause25762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom1450 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1450 Fin15AnchoredAtom4195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06312
  ] at hbad
  tauto

theorem fin15Anchored_clause25763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4195 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1654 Fin15AnchoredAtom4195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06312
  ] at hbad
  tauto

theorem fin15Anchored_clause25764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4196 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom4196 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10408
  ] at hbad
  tauto

theorem fin15Anchored_clause25765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4197 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom4197 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18600
  ] at hbad
  tauto

theorem fin15Anchored_clause25766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom4198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12456
  ] at hbad
  tauto

theorem fin15Anchored_clause25767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom4198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12456
  ] at hbad
  tauto

theorem fin15Anchored_clause25768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom4198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12456
  ] at hbad
  tauto

theorem fin15Anchored_clause25769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom4198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12456
  ] at hbad
  tauto

theorem fin15Anchored_clause25770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4198 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom4198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12456
  ] at hbad
  tauto

theorem fin15Anchored_clause25771 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom1384 Fin15AnchoredAtom1404
    Fin15AnchoredAtom1453 Fin15AnchoredAtom1657 Fin15AnchoredAtom4198 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12456
  ] at hbad
  tauto

theorem fin15Anchored_clause25772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom4199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20648
  ] at hbad
  tauto

theorem fin15Anchored_clause25773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom4199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20648
  ] at hbad
  tauto

theorem fin15Anchored_clause25774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom4199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20648
  ] at hbad
  tauto

theorem fin15Anchored_clause25775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom4199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20648
  ] at hbad
  tauto

theorem fin15Anchored_clause25776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4199 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom4199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20648
  ] at hbad
  tauto

theorem fin15Anchored_clause25777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom1385 Fin15AnchoredAtom1405
    Fin15AnchoredAtom1454 Fin15AnchoredAtom1658 Fin15AnchoredAtom4199 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20648
  ] at hbad
  tauto

theorem fin15Anchored_clause25778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom4200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24744
  ] at hbad
  tauto

theorem fin15Anchored_clause25779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom4200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24744
  ] at hbad
  tauto

theorem fin15Anchored_clause25780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom4200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24744
  ] at hbad
  tauto

theorem fin15Anchored_clause25781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom4200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24744
  ] at hbad
  tauto

theorem fin15Anchored_clause25782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4200 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom4200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24744
  ] at hbad
  tauto

theorem fin15Anchored_clause25783 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom1385 Fin15AnchoredAtom1406
    Fin15AnchoredAtom1455 Fin15AnchoredAtom1659 Fin15AnchoredAtom4200 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24744
  ] at hbad
  tauto

theorem fin15Anchored_clause25784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom4201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01832
  ] at hbad
  tauto

theorem fin15Anchored_clause25785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom4201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01832
  ] at hbad
  tauto

theorem fin15Anchored_clause25786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom4201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01832
  ] at hbad
  tauto

theorem fin15Anchored_clause25787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom4201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01832
  ] at hbad
  tauto

theorem fin15Anchored_clause25788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4201 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom4201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01832
  ] at hbad
  tauto

theorem fin15Anchored_clause25789 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4201 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom1387 Fin15AnchoredAtom1392
    Fin15AnchoredAtom1456 Fin15AnchoredAtom1660 Fin15AnchoredAtom4201 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01832
  ] at hbad
  tauto

theorem fin15Anchored_clause25790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom4203 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04904
  ] at hbad
  tauto

theorem fin15Anchored_clause25791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom4203 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04904
  ] at hbad
  tauto

theorem fin15Anchored_clause25792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom4203 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04904
  ] at hbad
  tauto

theorem fin15Anchored_clause25793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom4203 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04904
  ] at hbad
  tauto

theorem fin15Anchored_clause25794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4203 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom4203 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04904
  ] at hbad
  tauto

theorem fin15Anchored_clause25795 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4203 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom1389 Fin15AnchoredAtom1394
    Fin15AnchoredAtom1458 Fin15AnchoredAtom1662 Fin15AnchoredAtom4203 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04904
  ] at hbad
  tauto

theorem fin15Anchored_clause25796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom4204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09000
  ] at hbad
  tauto

theorem fin15Anchored_clause25797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom4204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09000
  ] at hbad
  tauto

theorem fin15Anchored_clause25798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom4204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09000
  ] at hbad
  tauto

theorem fin15Anchored_clause25799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1459 Fin15AnchoredAtom4204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09000
  ] at hbad
  tauto

theorem fin15Anchored_clause25800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4204 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom4204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09000
  ] at hbad
  tauto

theorem fin15Anchored_clause25801 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4204 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom1390 Fin15AnchoredAtom1395
    Fin15AnchoredAtom1459 Fin15AnchoredAtom1663 Fin15AnchoredAtom4204 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09000
  ] at hbad
  tauto

theorem fin15Anchored_clause25802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom4205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17192
  ] at hbad
  tauto

theorem fin15Anchored_clause25803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1391 Fin15AnchoredAtom4205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17192
  ] at hbad
  tauto

theorem fin15Anchored_clause25804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom4205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17192
  ] at hbad
  tauto

theorem fin15Anchored_clause25805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1460 Fin15AnchoredAtom4205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17192
  ] at hbad
  tauto

theorem fin15Anchored_clause25806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4205 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1664 Fin15AnchoredAtom4205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17192
  ] at hbad
  tauto

theorem fin15Anchored_clause25807 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4205 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom1391 Fin15AnchoredAtom1396
    Fin15AnchoredAtom1460 Fin15AnchoredAtom1664 Fin15AnchoredAtom4205 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17192
  ] at hbad
  tauto

theorem fin15Anchored_clause25808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom4207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05416
  ] at hbad
  tauto

theorem fin15Anchored_clause25809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom4207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05416
  ] at hbad
  tauto

theorem fin15Anchored_clause25810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom4207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05416
  ] at hbad
  tauto

theorem fin15Anchored_clause25811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom4207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05416
  ] at hbad
  tauto

theorem fin15Anchored_clause25812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4207 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom4207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05416
  ] at hbad
  tauto

theorem fin15Anchored_clause25813 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4207 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom1389 Fin15AnchoredAtom1398
    Fin15AnchoredAtom1462 Fin15AnchoredAtom1666 Fin15AnchoredAtom4207 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05416
  ] at hbad
  tauto

theorem fin15Anchored_clause25814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom4208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09512
  ] at hbad
  tauto

theorem fin15Anchored_clause25815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom4208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09512
  ] at hbad
  tauto

theorem fin15Anchored_clause25816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom4208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09512
  ] at hbad
  tauto

theorem fin15Anchored_clause25817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom4208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09512
  ] at hbad
  tauto

theorem fin15Anchored_clause25818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4208 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom4208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09512
  ] at hbad
  tauto

theorem fin15Anchored_clause25819 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom1390 Fin15AnchoredAtom1399
    Fin15AnchoredAtom1463 Fin15AnchoredAtom1667 Fin15AnchoredAtom4208 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09512
  ] at hbad
  tauto

theorem fin15Anchored_clause25820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom4209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17704
  ] at hbad
  tauto

theorem fin15Anchored_clause25821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1391 Fin15AnchoredAtom4209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17704
  ] at hbad
  tauto

theorem fin15Anchored_clause25822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom4209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17704
  ] at hbad
  tauto

theorem fin15Anchored_clause25823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4209 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1668 Fin15AnchoredAtom4209 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17704
  ] at hbad
  tauto

theorem fin15Anchored_clause25824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom4213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12584
  ] at hbad
  tauto

theorem fin15Anchored_clause25825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom4213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12584
  ] at hbad
  tauto

theorem fin15Anchored_clause25826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1468 Fin15AnchoredAtom4213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12584
  ] at hbad
  tauto

theorem fin15Anchored_clause25827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4213 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom4213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12584
  ] at hbad
  tauto

theorem fin15Anchored_clause25828 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4213 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom1390 Fin15AnchoredAtom1404
    Fin15AnchoredAtom1468 Fin15AnchoredAtom1672 Fin15AnchoredAtom4213 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12584
  ] at hbad
  tauto

theorem fin15Anchored_clause25829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom4214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20776
  ] at hbad
  tauto

theorem fin15Anchored_clause25830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1391 Fin15AnchoredAtom4214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20776
  ] at hbad
  tauto

theorem fin15Anchored_clause25831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom4214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20776
  ] at hbad
  tauto

theorem fin15Anchored_clause25832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1469 Fin15AnchoredAtom4214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20776
  ] at hbad
  tauto

theorem fin15Anchored_clause25833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4214 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1673 Fin15AnchoredAtom4214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20776
  ] at hbad
  tauto

theorem fin15Anchored_clause25834 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4214 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom1391 Fin15AnchoredAtom1405
    Fin15AnchoredAtom1469 Fin15AnchoredAtom1673 Fin15AnchoredAtom4214 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20776
  ] at hbad
  tauto

theorem fin15Anchored_clause25835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom4215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24872
  ] at hbad
  tauto

theorem fin15Anchored_clause25836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1391 Fin15AnchoredAtom4215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24872
  ] at hbad
  tauto

theorem fin15Anchored_clause25837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom4215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24872
  ] at hbad
  tauto

theorem fin15Anchored_clause25838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1470 Fin15AnchoredAtom4215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24872
  ] at hbad
  tauto

theorem fin15Anchored_clause25839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4215 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1674 Fin15AnchoredAtom4215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24872
  ] at hbad
  tauto

theorem fin15Anchored_clause25840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4215 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom1391 Fin15AnchoredAtom1406
    Fin15AnchoredAtom1470 Fin15AnchoredAtom1674 Fin15AnchoredAtom4215 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24872
  ] at hbad
  tauto

theorem fin15Anchored_clause25841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom4216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03624
  ] at hbad
  tauto

theorem fin15Anchored_clause25842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1393 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1393 Fin15AnchoredAtom4216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03624
  ] at hbad
  tauto

theorem fin15Anchored_clause25843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1397 Fin15AnchoredAtom4216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03624
  ] at hbad
  tauto

theorem fin15Anchored_clause25844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1471 Fin15AnchoredAtom4216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03624
  ] at hbad
  tauto

theorem fin15Anchored_clause25845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4216 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom4216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03624
  ] at hbad
  tauto

theorem fin15Anchored_clause25846 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4216 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1393 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1471 chi ∧
      Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom1393 Fin15AnchoredAtom1397
    Fin15AnchoredAtom1471 Fin15AnchoredAtom1675 Fin15AnchoredAtom4216 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03624
  ] at hbad
  tauto

theorem fin15Anchored_clause25847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom4217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05672
  ] at hbad
  tauto

theorem fin15Anchored_clause25848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom4217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05672
  ] at hbad
  tauto

theorem fin15Anchored_clause25849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom4217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05672
  ] at hbad
  tauto

theorem fin15Anchored_clause25850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom4217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05672
  ] at hbad
  tauto

theorem fin15Anchored_clause25851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4217 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom4217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05672
  ] at hbad
  tauto

theorem fin15Anchored_clause25852 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom1394 Fin15AnchoredAtom1398
    Fin15AnchoredAtom1472 Fin15AnchoredAtom1676 Fin15AnchoredAtom4217 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05672
  ] at hbad
  tauto

theorem fin15Anchored_clause25853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom4218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09768
  ] at hbad
  tauto

theorem fin15Anchored_clause25854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom4218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09768
  ] at hbad
  tauto

theorem fin15Anchored_clause25855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4218 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom4218 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09768
  ] at hbad
  tauto

end ErdosSzekeres

end
