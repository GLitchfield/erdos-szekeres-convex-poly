module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 203. -/

theorem fin15Anchored_clause25984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom4249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09416
  ] at hbad
  tauto

theorem fin15Anchored_clause25985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom4249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09416
  ] at hbad
  tauto

theorem fin15Anchored_clause25986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom4249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09416
  ] at hbad
  tauto

theorem fin15Anchored_clause25987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4249 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom4249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09416
  ] at hbad
  tauto

theorem fin15Anchored_clause25988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1448 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom1412 Fin15AnchoredAtom1427
    Fin15AnchoredAtom1448 Fin15AnchoredAtom1708 Fin15AnchoredAtom4249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09416
  ] at hbad
  tauto

theorem fin15Anchored_clause25989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom4250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17608
  ] at hbad
  tauto

theorem fin15Anchored_clause25990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom4250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17608
  ] at hbad
  tauto

theorem fin15Anchored_clause25991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom4250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17608
  ] at hbad
  tauto

theorem fin15Anchored_clause25992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom4250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17608
  ] at hbad
  tauto

theorem fin15Anchored_clause25993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4250 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom4250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17608
  ] at hbad
  tauto

theorem fin15Anchored_clause25994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1449 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom1413 Fin15AnchoredAtom1428
    Fin15AnchoredAtom1449 Fin15AnchoredAtom1709 Fin15AnchoredAtom4250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17608
  ] at hbad
  tauto

theorem fin15Anchored_clause25995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom4254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12488
  ] at hbad
  tauto

theorem fin15Anchored_clause25996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom4254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12488
  ] at hbad
  tauto

theorem fin15Anchored_clause25997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom4254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12488
  ] at hbad
  tauto

theorem fin15Anchored_clause25998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom4254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12488
  ] at hbad
  tauto

theorem fin15Anchored_clause25999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4254 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom4254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12488
  ] at hbad
  tauto

theorem fin15Anchored_clause26000 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1453 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom1412 Fin15AnchoredAtom1432
    Fin15AnchoredAtom1453 Fin15AnchoredAtom1713 Fin15AnchoredAtom4254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12488
  ] at hbad
  tauto

theorem fin15Anchored_clause26001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom4255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20680
  ] at hbad
  tauto

theorem fin15Anchored_clause26002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom4255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20680
  ] at hbad
  tauto

theorem fin15Anchored_clause26003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom4255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20680
  ] at hbad
  tauto

theorem fin15Anchored_clause26004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom4255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20680
  ] at hbad
  tauto

theorem fin15Anchored_clause26005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4255 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom4255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20680
  ] at hbad
  tauto

theorem fin15Anchored_clause26006 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1454 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom1413 Fin15AnchoredAtom1433
    Fin15AnchoredAtom1454 Fin15AnchoredAtom1714 Fin15AnchoredAtom4255 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20680
  ] at hbad
  tauto

theorem fin15Anchored_clause26007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom4256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24776
  ] at hbad
  tauto

theorem fin15Anchored_clause26008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom4256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24776
  ] at hbad
  tauto

theorem fin15Anchored_clause26009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom4256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24776
  ] at hbad
  tauto

theorem fin15Anchored_clause26010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom4256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24776
  ] at hbad
  tauto

theorem fin15Anchored_clause26011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4256 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom4256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24776
  ] at hbad
  tauto

theorem fin15Anchored_clause26012 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1455 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom1413 Fin15AnchoredAtom1434
    Fin15AnchoredAtom1455 Fin15AnchoredAtom1715 Fin15AnchoredAtom4256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24776
  ] at hbad
  tauto

theorem fin15Anchored_clause26013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom4257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01864
  ] at hbad
  tauto

theorem fin15Anchored_clause26014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom4257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01864
  ] at hbad
  tauto

theorem fin15Anchored_clause26015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom4257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01864
  ] at hbad
  tauto

theorem fin15Anchored_clause26016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom4257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01864
  ] at hbad
  tauto

theorem fin15Anchored_clause26017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4257 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom4257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01864
  ] at hbad
  tauto

theorem fin15Anchored_clause26018 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4257 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1456 chi ∧
      Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom1415 Fin15AnchoredAtom1420
    Fin15AnchoredAtom1456 Fin15AnchoredAtom1716 Fin15AnchoredAtom4257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01864
  ] at hbad
  tauto

theorem fin15Anchored_clause26019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom4259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04936
  ] at hbad
  tauto

theorem fin15Anchored_clause26020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom4259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04936
  ] at hbad
  tauto

theorem fin15Anchored_clause26021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom4259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04936
  ] at hbad
  tauto

theorem fin15Anchored_clause26022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom4259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04936
  ] at hbad
  tauto

theorem fin15Anchored_clause26023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4259 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom4259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04936
  ] at hbad
  tauto

theorem fin15Anchored_clause26024 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4259 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1458 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom1417 Fin15AnchoredAtom1422
    Fin15AnchoredAtom1458 Fin15AnchoredAtom1718 Fin15AnchoredAtom4259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04936
  ] at hbad
  tauto

theorem fin15Anchored_clause26025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom4260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09032
  ] at hbad
  tauto

theorem fin15Anchored_clause26026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom4260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09032
  ] at hbad
  tauto

theorem fin15Anchored_clause26027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom4260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09032
  ] at hbad
  tauto

theorem fin15Anchored_clause26028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1459 Fin15AnchoredAtom4260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09032
  ] at hbad
  tauto

theorem fin15Anchored_clause26029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4260 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom4260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09032
  ] at hbad
  tauto

theorem fin15Anchored_clause26030 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4260 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1459 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom1418 Fin15AnchoredAtom1423
    Fin15AnchoredAtom1459 Fin15AnchoredAtom1719 Fin15AnchoredAtom4260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09032
  ] at hbad
  tauto

theorem fin15Anchored_clause26031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom4261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17224
  ] at hbad
  tauto

theorem fin15Anchored_clause26032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1419 Fin15AnchoredAtom4261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17224
  ] at hbad
  tauto

theorem fin15Anchored_clause26033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom4261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17224
  ] at hbad
  tauto

theorem fin15Anchored_clause26034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1460 Fin15AnchoredAtom4261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17224
  ] at hbad
  tauto

theorem fin15Anchored_clause26035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4261 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1720 Fin15AnchoredAtom4261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17224
  ] at hbad
  tauto

theorem fin15Anchored_clause26036 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4261 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1460 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom1419 Fin15AnchoredAtom1424
    Fin15AnchoredAtom1460 Fin15AnchoredAtom1720 Fin15AnchoredAtom4261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17224
  ] at hbad
  tauto

theorem fin15Anchored_clause26037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom4263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05448
  ] at hbad
  tauto

theorem fin15Anchored_clause26038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom4263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05448
  ] at hbad
  tauto

theorem fin15Anchored_clause26039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom4263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05448
  ] at hbad
  tauto

theorem fin15Anchored_clause26040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4263 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom4263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05448
  ] at hbad
  tauto

theorem fin15Anchored_clause26041 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4263 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1462 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom1417 Fin15AnchoredAtom1426
    Fin15AnchoredAtom1462 Fin15AnchoredAtom1722 Fin15AnchoredAtom4263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05448
  ] at hbad
  tauto

theorem fin15Anchored_clause26042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom4264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09544
  ] at hbad
  tauto

theorem fin15Anchored_clause26043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom4264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09544
  ] at hbad
  tauto

theorem fin15Anchored_clause26044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom4264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09544
  ] at hbad
  tauto

theorem fin15Anchored_clause26045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom4264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09544
  ] at hbad
  tauto

theorem fin15Anchored_clause26046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4264 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1723 Fin15AnchoredAtom4264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09544
  ] at hbad
  tauto

theorem fin15Anchored_clause26047 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1463 chi ∧
      Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom1418 Fin15AnchoredAtom1427
    Fin15AnchoredAtom1463 Fin15AnchoredAtom1723 Fin15AnchoredAtom4264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09544
  ] at hbad
  tauto

theorem fin15Anchored_clause26048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom4265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17736
  ] at hbad
  tauto

theorem fin15Anchored_clause26049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1419 Fin15AnchoredAtom4265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17736
  ] at hbad
  tauto

theorem fin15Anchored_clause26050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom4265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17736
  ] at hbad
  tauto

theorem fin15Anchored_clause26051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1464 Fin15AnchoredAtom4265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17736
  ] at hbad
  tauto

theorem fin15Anchored_clause26052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4265 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1724 Fin15AnchoredAtom4265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17736
  ] at hbad
  tauto

theorem fin15Anchored_clause26053 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4265 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1464 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom1419 Fin15AnchoredAtom1428
    Fin15AnchoredAtom1464 Fin15AnchoredAtom1724 Fin15AnchoredAtom4265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17736
  ] at hbad
  tauto

theorem fin15Anchored_clause26054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom4269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12616
  ] at hbad
  tauto

theorem fin15Anchored_clause26055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom4269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12616
  ] at hbad
  tauto

theorem fin15Anchored_clause26056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom4269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12616
  ] at hbad
  tauto

theorem fin15Anchored_clause26057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1468 Fin15AnchoredAtom4269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12616
  ] at hbad
  tauto

theorem fin15Anchored_clause26058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4269 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom4269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12616
  ] at hbad
  tauto

theorem fin15Anchored_clause26059 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4269 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1468 chi ∧
      Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom1418 Fin15AnchoredAtom1432
    Fin15AnchoredAtom1468 Fin15AnchoredAtom1728 Fin15AnchoredAtom4269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12616
  ] at hbad
  tauto

theorem fin15Anchored_clause26060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom4270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20808
  ] at hbad
  tauto

theorem fin15Anchored_clause26061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1419 Fin15AnchoredAtom4270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20808
  ] at hbad
  tauto

theorem fin15Anchored_clause26062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom4270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20808
  ] at hbad
  tauto

theorem fin15Anchored_clause26063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1469 Fin15AnchoredAtom4270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20808
  ] at hbad
  tauto

theorem fin15Anchored_clause26064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4270 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1729 Fin15AnchoredAtom4270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20808
  ] at hbad
  tauto

theorem fin15Anchored_clause26065 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4270 chi ∧
      Fin15AnchoredAtom1417 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1469 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom1419 Fin15AnchoredAtom1433
    Fin15AnchoredAtom1469 Fin15AnchoredAtom1729 Fin15AnchoredAtom4270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20808
  ] at hbad
  tauto

theorem fin15Anchored_clause26066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom4271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24904
  ] at hbad
  tauto

theorem fin15Anchored_clause26067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1419 Fin15AnchoredAtom4271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24904
  ] at hbad
  tauto

theorem fin15Anchored_clause26068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom4271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24904
  ] at hbad
  tauto

theorem fin15Anchored_clause26069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1470 Fin15AnchoredAtom4271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24904
  ] at hbad
  tauto

theorem fin15Anchored_clause26070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4271 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1730 Fin15AnchoredAtom4271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24904
  ] at hbad
  tauto

theorem fin15Anchored_clause26071 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4271 chi ∧
      Fin15AnchoredAtom1418 chi ∧
      Fin15AnchoredAtom1419 chi ∧
      Fin15AnchoredAtom1434 chi ∧
      Fin15AnchoredAtom1470 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom1419 Fin15AnchoredAtom1434
    Fin15AnchoredAtom1470 Fin15AnchoredAtom1730 Fin15AnchoredAtom4271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24904
  ] at hbad
  tauto

theorem fin15Anchored_clause26072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4272 chi ∧
      ¬Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1471 Fin15AnchoredAtom4272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03656
  ] at hbad
  tauto

theorem fin15Anchored_clause26073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4272 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1731 Fin15AnchoredAtom4272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03656
  ] at hbad
  tauto

theorem fin15Anchored_clause26074 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4272 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1421 chi ∧
      Fin15AnchoredAtom1425 chi ∧
      Fin15AnchoredAtom1471 chi ∧
      Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom1421 Fin15AnchoredAtom1425
    Fin15AnchoredAtom1471 Fin15AnchoredAtom1731 Fin15AnchoredAtom4272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03656
  ] at hbad
  tauto

theorem fin15Anchored_clause26075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom4273 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05704
  ] at hbad
  tauto

theorem fin15Anchored_clause26076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom4273 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05704
  ] at hbad
  tauto

theorem fin15Anchored_clause26077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom4273 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05704
  ] at hbad
  tauto

theorem fin15Anchored_clause26078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom4273 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05704
  ] at hbad
  tauto

theorem fin15Anchored_clause26079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4273 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom4273 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05704
  ] at hbad
  tauto

theorem fin15Anchored_clause26080 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1426 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom1422 Fin15AnchoredAtom1426
    Fin15AnchoredAtom1472 Fin15AnchoredAtom1732 Fin15AnchoredAtom4273 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05704
  ] at hbad
  tauto

theorem fin15Anchored_clause26081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom4274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09800
  ] at hbad
  tauto

theorem fin15Anchored_clause26082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom4274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09800
  ] at hbad
  tauto

theorem fin15Anchored_clause26083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom4274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09800
  ] at hbad
  tauto

theorem fin15Anchored_clause26084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom4274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09800
  ] at hbad
  tauto

theorem fin15Anchored_clause26085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4274 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom4274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09800
  ] at hbad
  tauto

theorem fin15Anchored_clause26086 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1427 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom1423 Fin15AnchoredAtom1427
    Fin15AnchoredAtom1473 Fin15AnchoredAtom1733 Fin15AnchoredAtom4274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09800
  ] at hbad
  tauto

theorem fin15Anchored_clause26087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom4275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17992
  ] at hbad
  tauto

theorem fin15Anchored_clause26088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom4275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17992
  ] at hbad
  tauto

theorem fin15Anchored_clause26089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom4275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17992
  ] at hbad
  tauto

theorem fin15Anchored_clause26090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom4275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17992
  ] at hbad
  tauto

theorem fin15Anchored_clause26091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4275 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom4275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17992
  ] at hbad
  tauto

theorem fin15Anchored_clause26092 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom1420 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1428 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom1424 Fin15AnchoredAtom1428
    Fin15AnchoredAtom1474 Fin15AnchoredAtom1734 Fin15AnchoredAtom4275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17992
  ] at hbad
  tauto

theorem fin15Anchored_clause26093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4276 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom4276 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06728
  ] at hbad
  tauto

theorem fin15Anchored_clause26094 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4276 chi ∧
      Fin15AnchoredAtom1421 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1429 chi ∧
      Fin15AnchoredAtom1475 chi ∧
      Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1421 Fin15AnchoredAtom1422 Fin15AnchoredAtom1429
    Fin15AnchoredAtom1475 Fin15AnchoredAtom1735 Fin15AnchoredAtom4276 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06728
  ] at hbad
  tauto

theorem fin15Anchored_clause26095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4277 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom4277 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10824
  ] at hbad
  tauto

theorem fin15Anchored_clause26096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4278 chi ∧
      ¬Fin15AnchoredAtom1737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1737 Fin15AnchoredAtom4278 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19016
  ] at hbad
  tauto

theorem fin15Anchored_clause26097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom4279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12872
  ] at hbad
  tauto

theorem fin15Anchored_clause26098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom4279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12872
  ] at hbad
  tauto

theorem fin15Anchored_clause26099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom4279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12872
  ] at hbad
  tauto

theorem fin15Anchored_clause26100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom4279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12872
  ] at hbad
  tauto

theorem fin15Anchored_clause26101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4279 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom4279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12872
  ] at hbad
  tauto

theorem fin15Anchored_clause26102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1423 chi ∧
      Fin15AnchoredAtom1432 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom1423 Fin15AnchoredAtom1432
    Fin15AnchoredAtom1478 Fin15AnchoredAtom1738 Fin15AnchoredAtom4279 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12872
  ] at hbad
  tauto

theorem fin15Anchored_clause26103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom4280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21064
  ] at hbad
  tauto

theorem fin15Anchored_clause26104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom4280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21064
  ] at hbad
  tauto

theorem fin15Anchored_clause26105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom4280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21064
  ] at hbad
  tauto

theorem fin15Anchored_clause26106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom4280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21064
  ] at hbad
  tauto

theorem fin15Anchored_clause26107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4280 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom4280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21064
  ] at hbad
  tauto

theorem fin15Anchored_clause26108 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom1422 chi ∧
      Fin15AnchoredAtom1424 chi ∧
      Fin15AnchoredAtom1433 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom1424 Fin15AnchoredAtom1433
    Fin15AnchoredAtom1479 Fin15AnchoredAtom1739 Fin15AnchoredAtom4280 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21064
  ] at hbad
  tauto

theorem fin15Anchored_clause26109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom4281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25160
  ] at hbad
  tauto

theorem fin15Anchored_clause26110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom4281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25160
  ] at hbad
  tauto

theorem fin15Anchored_clause26111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4281 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom4281 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25160
  ] at hbad
  tauto

end ErdosSzekeres

end
