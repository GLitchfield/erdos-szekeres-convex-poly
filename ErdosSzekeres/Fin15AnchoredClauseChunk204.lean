module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 204. -/

theorem fin15Anchored_clause26112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom4281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25160
  ] at hbad
  tauto

theorem fin15Anchored_clause26113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom4281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25160
  ] at hbad
  tauto

theorem fin15Anchored_clause26114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom1424 Fin15AnchoredAtom1434
    Fin15AnchoredAtom1480 Fin15AnchoredAtom1740 Fin15AnchoredAtom4281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25160
  ] at hbad
  tauto

theorem fin15Anchored_clause26115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4282 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom4282 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07240
  ] at hbad
  tauto

theorem fin15Anchored_clause26116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4282 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1741 Fin15AnchoredAtom4282 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07240
  ] at hbad
  tauto

theorem fin15Anchored_clause26117 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4282 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1429 chi ∧
      Fin15AnchoredAtom1481 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1425 Fin15AnchoredAtom1426 Fin15AnchoredAtom1429
    Fin15AnchoredAtom1481 Fin15AnchoredAtom1741 Fin15AnchoredAtom4282 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07240
  ] at hbad
  tauto

theorem fin15Anchored_clause26118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom4285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13384
  ] at hbad
  tauto

theorem fin15Anchored_clause26119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom4285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13384
  ] at hbad
  tauto

theorem fin15Anchored_clause26120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom4285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13384
  ] at hbad
  tauto

theorem fin15Anchored_clause26121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom4285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13384
  ] at hbad
  tauto

theorem fin15Anchored_clause26122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4285 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom4285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13384
  ] at hbad
  tauto

theorem fin15Anchored_clause26123 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom1427 Fin15AnchoredAtom1432
    Fin15AnchoredAtom1484 Fin15AnchoredAtom1744 Fin15AnchoredAtom4285 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13384
  ] at hbad
  tauto

theorem fin15Anchored_clause26124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom4286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21576
  ] at hbad
  tauto

theorem fin15Anchored_clause26125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom4286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21576
  ] at hbad
  tauto

theorem fin15Anchored_clause26126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom4286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21576
  ] at hbad
  tauto

theorem fin15Anchored_clause26127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom4286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21576
  ] at hbad
  tauto

theorem fin15Anchored_clause26128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4286 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom4286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21576
  ] at hbad
  tauto

theorem fin15Anchored_clause26129 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom1428 Fin15AnchoredAtom1433
    Fin15AnchoredAtom1485 Fin15AnchoredAtom1745 Fin15AnchoredAtom4286 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21576
  ] at hbad
  tauto

theorem fin15Anchored_clause26130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom4287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25672
  ] at hbad
  tauto

theorem fin15Anchored_clause26131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom4287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25672
  ] at hbad
  tauto

theorem fin15Anchored_clause26132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom4287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25672
  ] at hbad
  tauto

theorem fin15Anchored_clause26133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom4287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25672
  ] at hbad
  tauto

theorem fin15Anchored_clause26134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4287 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom4287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25672
  ] at hbad
  tauto

theorem fin15Anchored_clause26135 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom1428 Fin15AnchoredAtom1434
    Fin15AnchoredAtom1486 Fin15AnchoredAtom1746 Fin15AnchoredAtom4287 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25672
  ] at hbad
  tauto

theorem fin15Anchored_clause26136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4288 chi ∧
      Fin15AnchoredAtom1429 chi ∧
      Fin15AnchoredAtom1430 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1487 chi ∧
      Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1429 Fin15AnchoredAtom1430 Fin15AnchoredAtom1432
    Fin15AnchoredAtom1487 Fin15AnchoredAtom1747 Fin15AnchoredAtom4288 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14408
  ] at hbad
  tauto

theorem fin15Anchored_clause26137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom4291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28744
  ] at hbad
  tauto

theorem fin15Anchored_clause26138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom4291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28744
  ] at hbad
  tauto

theorem fin15Anchored_clause26139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom4291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28744
  ] at hbad
  tauto

theorem fin15Anchored_clause26140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom4291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28744
  ] at hbad
  tauto

theorem fin15Anchored_clause26141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4291 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom4291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28744
  ] at hbad
  tauto

theorem fin15Anchored_clause26142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom1433 Fin15AnchoredAtom1434
    Fin15AnchoredAtom1490 Fin15AnchoredAtom1750 Fin15AnchoredAtom4291 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28744
  ] at hbad
  tauto

theorem fin15Anchored_clause26143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom4292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01928
  ] at hbad
  tauto

theorem fin15Anchored_clause26144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom4292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01928
  ] at hbad
  tauto

theorem fin15Anchored_clause26145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom4292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01928
  ] at hbad
  tauto

theorem fin15Anchored_clause26146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4292 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom4292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01928
  ] at hbad
  tauto

theorem fin15Anchored_clause26147 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4292 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom1436 Fin15AnchoredAtom1441
    Fin15AnchoredAtom1456 Fin15AnchoredAtom1751 Fin15AnchoredAtom4292 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01928
  ] at hbad
  tauto

theorem fin15Anchored_clause26148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom4294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05000
  ] at hbad
  tauto

theorem fin15Anchored_clause26149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom4294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05000
  ] at hbad
  tauto

theorem fin15Anchored_clause26150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom4294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05000
  ] at hbad
  tauto

theorem fin15Anchored_clause26151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4294 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom4294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05000
  ] at hbad
  tauto

theorem fin15Anchored_clause26152 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4294 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom1438 Fin15AnchoredAtom1443
    Fin15AnchoredAtom1458 Fin15AnchoredAtom1753 Fin15AnchoredAtom4294 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05000
  ] at hbad
  tauto

theorem fin15Anchored_clause26153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom4295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09096
  ] at hbad
  tauto

theorem fin15Anchored_clause26154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1439 Fin15AnchoredAtom4295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09096
  ] at hbad
  tauto

theorem fin15Anchored_clause26155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom4295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09096
  ] at hbad
  tauto

theorem fin15Anchored_clause26156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4295 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom4295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09096
  ] at hbad
  tauto

theorem fin15Anchored_clause26157 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4295 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom1439 Fin15AnchoredAtom1444
    Fin15AnchoredAtom1459 Fin15AnchoredAtom1754 Fin15AnchoredAtom4295 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09096
  ] at hbad
  tauto

theorem fin15Anchored_clause26158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom4296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17288
  ] at hbad
  tauto

theorem fin15Anchored_clause26159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1440 Fin15AnchoredAtom4296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17288
  ] at hbad
  tauto

theorem fin15Anchored_clause26160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom4296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17288
  ] at hbad
  tauto

theorem fin15Anchored_clause26161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1460 Fin15AnchoredAtom4296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17288
  ] at hbad
  tauto

theorem fin15Anchored_clause26162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4296 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1755 Fin15AnchoredAtom4296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17288
  ] at hbad
  tauto

theorem fin15Anchored_clause26163 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4296 chi ∧
      Fin15AnchoredAtom1435 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom1440 Fin15AnchoredAtom1445
    Fin15AnchoredAtom1460 Fin15AnchoredAtom1755 Fin15AnchoredAtom4296 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17288
  ] at hbad
  tauto

theorem fin15Anchored_clause26164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom4298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05512
  ] at hbad
  tauto

theorem fin15Anchored_clause26165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom4298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05512
  ] at hbad
  tauto

theorem fin15Anchored_clause26166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom4298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05512
  ] at hbad
  tauto

theorem fin15Anchored_clause26167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4298 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom4298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05512
  ] at hbad
  tauto

theorem fin15Anchored_clause26168 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4298 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom1438 Fin15AnchoredAtom1447
    Fin15AnchoredAtom1462 Fin15AnchoredAtom1757 Fin15AnchoredAtom4298 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05512
  ] at hbad
  tauto

theorem fin15Anchored_clause26169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom4299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09608
  ] at hbad
  tauto

theorem fin15Anchored_clause26170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1439 Fin15AnchoredAtom4299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09608
  ] at hbad
  tauto

theorem fin15Anchored_clause26171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom4299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09608
  ] at hbad
  tauto

theorem fin15Anchored_clause26172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom4299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09608
  ] at hbad
  tauto

theorem fin15Anchored_clause26173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4299 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom4299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09608
  ] at hbad
  tauto

theorem fin15Anchored_clause26174 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4299 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom1439 Fin15AnchoredAtom1448
    Fin15AnchoredAtom1463 Fin15AnchoredAtom1758 Fin15AnchoredAtom4299 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09608
  ] at hbad
  tauto

theorem fin15Anchored_clause26175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom4300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17800
  ] at hbad
  tauto

theorem fin15Anchored_clause26176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1440 Fin15AnchoredAtom4300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17800
  ] at hbad
  tauto

theorem fin15Anchored_clause26177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom4300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17800
  ] at hbad
  tauto

theorem fin15Anchored_clause26178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1464 Fin15AnchoredAtom4300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17800
  ] at hbad
  tauto

theorem fin15Anchored_clause26179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4300 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1759 Fin15AnchoredAtom4300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17800
  ] at hbad
  tauto

theorem fin15Anchored_clause26180 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4300 chi ∧
      Fin15AnchoredAtom1436 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom1440 Fin15AnchoredAtom1449
    Fin15AnchoredAtom1464 Fin15AnchoredAtom1759 Fin15AnchoredAtom4300 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17800
  ] at hbad
  tauto

theorem fin15Anchored_clause26181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom4304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12680
  ] at hbad
  tauto

theorem fin15Anchored_clause26182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1439 Fin15AnchoredAtom4304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12680
  ] at hbad
  tauto

theorem fin15Anchored_clause26183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom4304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12680
  ] at hbad
  tauto

theorem fin15Anchored_clause26184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1468 Fin15AnchoredAtom4304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12680
  ] at hbad
  tauto

theorem fin15Anchored_clause26185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4304 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom4304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12680
  ] at hbad
  tauto

theorem fin15Anchored_clause26186 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4304 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom1439 Fin15AnchoredAtom1453
    Fin15AnchoredAtom1468 Fin15AnchoredAtom1763 Fin15AnchoredAtom4304 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12680
  ] at hbad
  tauto

theorem fin15Anchored_clause26187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom4305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20872
  ] at hbad
  tauto

theorem fin15Anchored_clause26188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1440 Fin15AnchoredAtom4305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20872
  ] at hbad
  tauto

theorem fin15Anchored_clause26189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom4305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20872
  ] at hbad
  tauto

theorem fin15Anchored_clause26190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1469 Fin15AnchoredAtom4305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20872
  ] at hbad
  tauto

theorem fin15Anchored_clause26191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4305 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1764 Fin15AnchoredAtom4305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20872
  ] at hbad
  tauto

theorem fin15Anchored_clause26192 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4305 chi ∧
      Fin15AnchoredAtom1438 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom1440 Fin15AnchoredAtom1454
    Fin15AnchoredAtom1469 Fin15AnchoredAtom1764 Fin15AnchoredAtom4305 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20872
  ] at hbad
  tauto

theorem fin15Anchored_clause26193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1439 Fin15AnchoredAtom4306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24968
  ] at hbad
  tauto

theorem fin15Anchored_clause26194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1440 Fin15AnchoredAtom4306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24968
  ] at hbad
  tauto

theorem fin15Anchored_clause26195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom4306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24968
  ] at hbad
  tauto

theorem fin15Anchored_clause26196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4306 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1765 Fin15AnchoredAtom4306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24968
  ] at hbad
  tauto

theorem fin15Anchored_clause26197 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4306 chi ∧
      Fin15AnchoredAtom1439 chi ∧
      Fin15AnchoredAtom1440 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1439 Fin15AnchoredAtom1440 Fin15AnchoredAtom1455
    Fin15AnchoredAtom1470 Fin15AnchoredAtom1765 Fin15AnchoredAtom4306 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24968
  ] at hbad
  tauto

theorem fin15Anchored_clause26198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4307 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom4307 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03720
  ] at hbad
  tauto

theorem fin15Anchored_clause26199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4307 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom4307 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03720
  ] at hbad
  tauto

theorem fin15Anchored_clause26200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom4308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05768
  ] at hbad
  tauto

theorem fin15Anchored_clause26201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom4308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05768
  ] at hbad
  tauto

theorem fin15Anchored_clause26202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom4308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05768
  ] at hbad
  tauto

theorem fin15Anchored_clause26203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom4308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05768
  ] at hbad
  tauto

theorem fin15Anchored_clause26204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4308 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom4308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05768
  ] at hbad
  tauto

theorem fin15Anchored_clause26205 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1447 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom1443 Fin15AnchoredAtom1447
    Fin15AnchoredAtom1472 Fin15AnchoredAtom1767 Fin15AnchoredAtom4308 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05768
  ] at hbad
  tauto

theorem fin15Anchored_clause26206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom4309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09864
  ] at hbad
  tauto

theorem fin15Anchored_clause26207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom4309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09864
  ] at hbad
  tauto

theorem fin15Anchored_clause26208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom4309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09864
  ] at hbad
  tauto

theorem fin15Anchored_clause26209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom4309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09864
  ] at hbad
  tauto

theorem fin15Anchored_clause26210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4309 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom4309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09864
  ] at hbad
  tauto

theorem fin15Anchored_clause26211 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom1444 Fin15AnchoredAtom1448
    Fin15AnchoredAtom1473 Fin15AnchoredAtom1768 Fin15AnchoredAtom4309 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09864
  ] at hbad
  tauto

theorem fin15Anchored_clause26212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom4310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18056
  ] at hbad
  tauto

theorem fin15Anchored_clause26213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom4310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18056
  ] at hbad
  tauto

theorem fin15Anchored_clause26214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom4310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18056
  ] at hbad
  tauto

theorem fin15Anchored_clause26215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom4310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18056
  ] at hbad
  tauto

theorem fin15Anchored_clause26216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4310 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom4310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18056
  ] at hbad
  tauto

theorem fin15Anchored_clause26217 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom1441 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom1445 Fin15AnchoredAtom1449
    Fin15AnchoredAtom1474 Fin15AnchoredAtom1769 Fin15AnchoredAtom4310 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18056
  ] at hbad
  tauto

theorem fin15Anchored_clause26218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4311 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom4311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06792
  ] at hbad
  tauto

theorem fin15Anchored_clause26219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4311 chi ∧
      ¬Fin15AnchoredAtom1450 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1450 Fin15AnchoredAtom4311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06792
  ] at hbad
  tauto

theorem fin15Anchored_clause26220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4311 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1770 Fin15AnchoredAtom4311 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06792
  ] at hbad
  tauto

theorem fin15Anchored_clause26221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4312 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom4312 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10888
  ] at hbad
  tauto

theorem fin15Anchored_clause26222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4313 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom4313 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19080
  ] at hbad
  tauto

theorem fin15Anchored_clause26223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom4314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12936
  ] at hbad
  tauto

theorem fin15Anchored_clause26224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom4314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12936
  ] at hbad
  tauto

theorem fin15Anchored_clause26225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom4314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12936
  ] at hbad
  tauto

theorem fin15Anchored_clause26226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom4314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12936
  ] at hbad
  tauto

theorem fin15Anchored_clause26227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4314 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom4314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12936
  ] at hbad
  tauto

theorem fin15Anchored_clause26228 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1444 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom1444 Fin15AnchoredAtom1453
    Fin15AnchoredAtom1478 Fin15AnchoredAtom1773 Fin15AnchoredAtom4314 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12936
  ] at hbad
  tauto

theorem fin15Anchored_clause26229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom4315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21128
  ] at hbad
  tauto

theorem fin15Anchored_clause26230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom4315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21128
  ] at hbad
  tauto

theorem fin15Anchored_clause26231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom4315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21128
  ] at hbad
  tauto

theorem fin15Anchored_clause26232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom4315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21128
  ] at hbad
  tauto

theorem fin15Anchored_clause26233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4315 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom4315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21128
  ] at hbad
  tauto

theorem fin15Anchored_clause26234 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom1443 chi ∧
      Fin15AnchoredAtom1445 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom1445 Fin15AnchoredAtom1454
    Fin15AnchoredAtom1479 Fin15AnchoredAtom1774 Fin15AnchoredAtom4315 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21128
  ] at hbad
  tauto

theorem fin15Anchored_clause26235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom4316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25224
  ] at hbad
  tauto

theorem fin15Anchored_clause26236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom4316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25224
  ] at hbad
  tauto

theorem fin15Anchored_clause26237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom4316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25224
  ] at hbad
  tauto

theorem fin15Anchored_clause26238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom4316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25224
  ] at hbad
  tauto

theorem fin15Anchored_clause26239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4316 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom4316 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25224
  ] at hbad
  tauto

end ErdosSzekeres

end
