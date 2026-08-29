module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 070. -/

theorem predecessorHalfFin13_clause19941 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom1465 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4545
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19942 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom1465 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4545
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19943 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom1465 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4545
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19944 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1465 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0480
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom1465 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4545
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19945 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom1466 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1729
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19946 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom1466 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1729
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19947 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom1466 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1729
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19948 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom1466 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1729
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19949 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1466 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom1466 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1729
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19957 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom1468 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19958 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom1468 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19959 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom1468 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19960 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom1468 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19961 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1468 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom1468 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19962 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1468 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0483
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom1468 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4801
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19969 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom1470 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19970 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom1470 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19971 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom1470 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19972 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom1470 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19973 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1470 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom1470 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5313
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19981 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom1472 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1857
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19982 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom1472 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1857
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19983 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom1472 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1857
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19984 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom1472 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1857
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19985 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1472 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0977 PredecessorHalfFin13Atom1472 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1857
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19993 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom1474 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19994 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom1474 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19995 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom1474 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19996 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom1474 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19997 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1474 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom1474 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19998 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1474 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0483
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0979 PredecessorHalfFin13Atom1474 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20005 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom1476 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20006 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom1476 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20007 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom1476 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20008 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom1476 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20009 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1476 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0981 PredecessorHalfFin13Atom1476 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20023 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom1479 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20024 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom1479 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20025 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom1479 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20026 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom1479 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20027 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1479 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0984 PredecessorHalfFin13Atom1479 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20041 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom1482 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1921
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20042 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom1482 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1921
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20043 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom1482 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1921
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20044 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom1482 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1921
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20045 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1482 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0987 PredecessorHalfFin13Atom1482 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1921
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20053 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom1484 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4993
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20054 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom1484 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4993
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20055 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom1484 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4993
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20056 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom1484 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4993
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20057 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1484 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0989 PredecessorHalfFin13Atom1484 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4993
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20065 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom1486 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5505
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20066 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom1486 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5505
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20067 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom1486 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5505
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20068 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom1486 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5505
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20069 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1486 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom1486 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5505
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20070 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1486 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0991 PredecessorHalfFin13Atom1486 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5505
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20083 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom1489 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5761
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20084 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom1489 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5761
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20085 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom1489 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5761
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20086 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom1489 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5761
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20087 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1489 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom1489 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5761
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20088 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1489 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0495
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0994 PredecessorHalfFin13Atom1489 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5761
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20107 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom1493 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5889
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20108 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom1493 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5889
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20109 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom1493 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5889
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20110 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom1493 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5889
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause20111 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1493 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0998 PredecessorHalfFin13Atom1493 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5889
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22111 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom1827 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22112 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom1827 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22113 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom1827 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22114 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0708 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom1827 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22115 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1827 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom1827 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22116 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1827 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0708 chi ∧
      PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0680
    PredecessorHalfFin13Atom0708 PredecessorHalfFin13Atom0792 PredecessorHalfFin13Atom1827 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0124
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22117 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom1828 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22118 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom1828 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22119 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom1828 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22120 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0709 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom1828 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22121 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1828 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom1828 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22122 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1828 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0709 chi ∧
      PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0681
    PredecessorHalfFin13Atom0709 PredecessorHalfFin13Atom0793 PredecessorHalfFin13Atom1828 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22123 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom1829 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22124 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom1829 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22125 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom1829 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22126 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0710 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom1829 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22127 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1829 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom1829 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22128 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1829 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0710 chi ∧
      PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0682
    PredecessorHalfFin13Atom0710 PredecessorHalfFin13Atom0794 PredecessorHalfFin13Atom1829 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0316
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22129 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom1830 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0572
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22130 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom1830 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0572
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22131 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom1830 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0572
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22132 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0711 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom1830 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0572
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22133 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1830 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom1830 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0572
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22134 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1830 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0711 chi ∧
      PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0683
    PredecessorHalfFin13Atom0711 PredecessorHalfFin13Atom0795 PredecessorHalfFin13Atom1830 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0572
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22135 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom1831 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1084
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22136 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0677 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom1831 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1084
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22137 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom1831 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1084
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22138 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0712 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom1831 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1084
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22139 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1831 chi ∧
      ¬PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom1831 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1084
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22140 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1831 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0677 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0712 chi ∧
      PredecessorHalfFin13Atom0796 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0677 PredecessorHalfFin13Atom0684
    PredecessorHalfFin13Atom0712 PredecessorHalfFin13Atom0796 PredecessorHalfFin13Atom1831 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1084
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22141 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom1832 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2108
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22142 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0678 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0678 PredecessorHalfFin13Atom1832 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2108
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22143 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom1832 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2108
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22144 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0713 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0713 PredecessorHalfFin13Atom1832 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2108
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22145 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1832 chi ∧
      ¬PredecessorHalfFin13Atom0797 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0797 PredecessorHalfFin13Atom1832 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2108
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22147 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom1833 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22148 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0679 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom1833 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22149 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom1833 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22150 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0714 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom1833 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22151 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1833 chi ∧
      ¬PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom1833 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22152 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1833 chi ∧
      PredecessorHalfFin13Atom0672 chi ∧
      PredecessorHalfFin13Atom0679 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0714 chi ∧
      PredecessorHalfFin13Atom0798 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0672 PredecessorHalfFin13Atom0679 PredecessorHalfFin13Atom0686
    PredecessorHalfFin13Atom0714 PredecessorHalfFin13Atom0798 PredecessorHalfFin13Atom1833 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22153 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom1834 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22154 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom1834 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22155 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom1834 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22156 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0715 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom1834 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22157 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1834 chi ∧
      ¬PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom1834 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22158 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1834 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0674 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0715 chi ∧
      PredecessorHalfFin13Atom0799 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0674 PredecessorHalfFin13Atom0687
    PredecessorHalfFin13Atom0715 PredecessorHalfFin13Atom0799 PredecessorHalfFin13Atom1834 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22159 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom1835 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22160 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom1835 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22161 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom1835 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22162 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0716 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom1835 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22163 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1835 chi ∧
      ¬PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom1835 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22164 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1835 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0675 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0716 chi ∧
      PredecessorHalfFin13Atom0800 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0675 PredecessorHalfFin13Atom0688
    PredecessorHalfFin13Atom0716 PredecessorHalfFin13Atom0800 PredecessorHalfFin13Atom1835 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22165 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom1836 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22166 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom1836 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22167 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom1836 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22168 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0717 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom1836 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22169 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1836 chi ∧
      ¬PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom1836 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22170 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1836 chi ∧
      PredecessorHalfFin13Atom0673 chi ∧
      PredecessorHalfFin13Atom0676 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0717 chi ∧
      PredecessorHalfFin13Atom0801 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom0676 PredecessorHalfFin13Atom0689
    PredecessorHalfFin13Atom0717 PredecessorHalfFin13Atom0801 PredecessorHalfFin13Atom1836 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22171 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1837 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0673 PredecessorHalfFin13Atom1837 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1116
  ] at hbad
  tauto

end ErdosSzekeres

end
