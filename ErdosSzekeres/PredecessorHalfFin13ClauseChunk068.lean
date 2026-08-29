module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 068. -/

theorem predecessorHalfFin13_clause19479 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom1388 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4657
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19480 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom1388 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4657
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1388 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom1388 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4657
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19482 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1388 chi ∧
      PredecessorHalfFin13Atom0426 chi ∧
      PredecessorHalfFin13Atom0429 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0426 PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom1388 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4657
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19489 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0427 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0427 PredecessorHalfFin13Atom1390 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5169
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19490 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0429 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0429 PredecessorHalfFin13Atom1390 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5169
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19491 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom1390 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5169
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19492 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom1390 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5169
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19493 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1390 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom1390 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5169
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19501 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom1392 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0465
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19502 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom1392 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0465
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19503 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom1392 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0465
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19504 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom1392 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0465
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19505 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1392 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom1392 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0465
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19506 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1392 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0436
    PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom1392 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0465
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19507 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom1393 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0721
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19508 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom1393 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0721
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19509 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom1393 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0721
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19510 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom1393 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0721
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19511 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1393 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom1393 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0721
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19512 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1393 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0437
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom1393 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0721
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19513 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom1394 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19514 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom1394 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19515 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom1394 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19516 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom1394 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19517 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1394 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom1394 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19518 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1394 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0438
    PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom1394 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1233
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19525 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0430 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom1396 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19526 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom1396 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19527 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom1396 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19528 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom1396 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19529 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1396 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom1396 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19530 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1396 chi ∧
      PredecessorHalfFin13Atom0430 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0430 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0440
    PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom1396 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4305
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19531 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom1397 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0849
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19532 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom1397 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0849
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19533 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom1397 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0849
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19534 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom1397 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0849
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19535 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1397 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom1397 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0849
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19536 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1397 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom1397 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0849
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19537 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom1398 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19538 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom1398 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19539 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom1398 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19540 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom1398 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19541 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1398 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom1398 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19542 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1398 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom1398 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1361
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19549 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom1400 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19550 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom1400 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19551 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom1400 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19552 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom1400 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom1400 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19554 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1400 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0431 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom1400 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4433
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19555 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom1401 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19556 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom1401 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom1401 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19558 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom1401 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19559 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom1401 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19560 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1401 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom1401 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1617
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19567 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom1403 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19568 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom1403 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19569 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom1403 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19570 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom1403 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19571 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom1403 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19572 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1403 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0432 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom1403 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4689
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19579 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom1405 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19580 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom1405 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom1405 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19582 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom1405 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom1405 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19584 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1405 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0433 PredecessorHalfFin13Atom0435 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom1405 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5201
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19591 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom1407 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0913
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19592 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom1407 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0913
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19593 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom1407 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0913
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19594 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom1407 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0913
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19595 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom1407 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0913
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19596 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1407 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0441
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom1407 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0913
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19597 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom1408 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19598 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom1408 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19599 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom1408 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19600 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom1408 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom1408 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19602 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1408 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0442
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom1408 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1425
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19609 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom1410 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4497
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19610 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom1410 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4497
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19611 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom1410 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4497
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19612 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom1410 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4497
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19613 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom1410 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4497
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19614 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1410 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0436 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0444
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom1410 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4497
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19615 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom1411 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19616 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom1411 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19617 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom1411 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19618 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom1411 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19619 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom1411 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19620 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1411 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0445
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom1411 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1681
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19627 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom1413 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4753
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19628 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom1413 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4753
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19629 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom1413 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4753
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19630 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom1413 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4753
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19631 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom1413 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4753
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19632 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1413 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0437 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom1413 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4753
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19639 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom1415 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19640 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom1415 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19641 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom1415 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19642 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom1415 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19643 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom1415 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19644 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1415 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0438 PredecessorHalfFin13Atom0440 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom1415 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5265
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19651 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom1417 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19652 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom1417 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19653 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom1417 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19654 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom1417 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19655 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom1417 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1809
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19663 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom1419 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4881
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19664 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom1419 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4881
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19665 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom1419 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4881
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19666 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom1419 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4881
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19667 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom1419 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4881
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19668 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1419 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0441 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0447
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom1419 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4881
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19675 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom1421 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19676 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom1421 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19677 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom1421 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19678 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom1421 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19679 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom1421 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19680 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1421 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0442 PredecessorHalfFin13Atom0444 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom1421 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5393
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19693 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom1424 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19694 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom1424 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19695 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0449 PredecessorHalfFin13Atom1424 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19696 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom1424 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19697 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom1424 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5649
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19698 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1424 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0445 PredecessorHalfFin13Atom0447 PredecessorHalfFin13Atom0449
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom1424 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5649
  ] at hbad
  tauto

end ErdosSzekeres

end
