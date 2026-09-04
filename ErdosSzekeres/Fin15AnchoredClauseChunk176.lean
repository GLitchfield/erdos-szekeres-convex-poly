module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 176. -/

theorem fin15Anchored_clause22528 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3335 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom0989 Fin15AnchoredAtom1002
    Fin15AnchoredAtom1030 Fin15AnchoredAtom1619 Fin15AnchoredAtom3335 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01378
  ] at hbad
  tauto

theorem fin15Anchored_clause22529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom3337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04450
  ] at hbad
  tauto

theorem fin15Anchored_clause22530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom3337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04450
  ] at hbad
  tauto

theorem fin15Anchored_clause22531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom3337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04450
  ] at hbad
  tauto

theorem fin15Anchored_clause22532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3337 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom3337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04450
  ] at hbad
  tauto

theorem fin15Anchored_clause22533 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3337 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom0991 Fin15AnchoredAtom1004
    Fin15AnchoredAtom1032 Fin15AnchoredAtom1621 Fin15AnchoredAtom3337 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04450
  ] at hbad
  tauto

theorem fin15Anchored_clause22534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom3338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08546
  ] at hbad
  tauto

theorem fin15Anchored_clause22535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom3338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08546
  ] at hbad
  tauto

theorem fin15Anchored_clause22536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom3338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08546
  ] at hbad
  tauto

theorem fin15Anchored_clause22537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom3338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08546
  ] at hbad
  tauto

theorem fin15Anchored_clause22538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3338 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom3338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08546
  ] at hbad
  tauto

theorem fin15Anchored_clause22539 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3338 chi ∧
      Fin15AnchoredAtom0987 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom0992 Fin15AnchoredAtom1005
    Fin15AnchoredAtom1033 Fin15AnchoredAtom1622 Fin15AnchoredAtom3338 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08546
  ] at hbad
  tauto

theorem fin15Anchored_clause22540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0987 Fin15AnchoredAtom3339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16738
  ] at hbad
  tauto

theorem fin15Anchored_clause22541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom3339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16738
  ] at hbad
  tauto

theorem fin15Anchored_clause22542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1006 Fin15AnchoredAtom3339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16738
  ] at hbad
  tauto

theorem fin15Anchored_clause22543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1034 Fin15AnchoredAtom3339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16738
  ] at hbad
  tauto

theorem fin15Anchored_clause22544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3339 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1623 Fin15AnchoredAtom3339 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16738
  ] at hbad
  tauto

theorem fin15Anchored_clause22545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom3340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01634
  ] at hbad
  tauto

theorem fin15Anchored_clause22546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom3340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01634
  ] at hbad
  tauto

theorem fin15Anchored_clause22547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom3340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01634
  ] at hbad
  tauto

theorem fin15Anchored_clause22548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom3340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01634
  ] at hbad
  tauto

theorem fin15Anchored_clause22549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom3340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01634
  ] at hbad
  tauto

theorem fin15Anchored_clause22550 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom0989 Fin15AnchoredAtom1007
    Fin15AnchoredAtom1035 Fin15AnchoredAtom1624 Fin15AnchoredAtom3340 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01634
  ] at hbad
  tauto

theorem fin15Anchored_clause22551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3341 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom3341 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02658
  ] at hbad
  tauto

theorem fin15Anchored_clause22552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom3342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04706
  ] at hbad
  tauto

theorem fin15Anchored_clause22553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom3342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04706
  ] at hbad
  tauto

theorem fin15Anchored_clause22554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom3342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04706
  ] at hbad
  tauto

theorem fin15Anchored_clause22555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom3342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04706
  ] at hbad
  tauto

theorem fin15Anchored_clause22556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom3342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04706
  ] at hbad
  tauto

theorem fin15Anchored_clause22557 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom0991 Fin15AnchoredAtom1009
    Fin15AnchoredAtom1037 Fin15AnchoredAtom1626 Fin15AnchoredAtom3342 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04706
  ] at hbad
  tauto

theorem fin15Anchored_clause22558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom3343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08802
  ] at hbad
  tauto

theorem fin15Anchored_clause22559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom3343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08802
  ] at hbad
  tauto

theorem fin15Anchored_clause22560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom3343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08802
  ] at hbad
  tauto

theorem fin15Anchored_clause22561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom3343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08802
  ] at hbad
  tauto

theorem fin15Anchored_clause22562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom3343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08802
  ] at hbad
  tauto

theorem fin15Anchored_clause22563 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom0992 Fin15AnchoredAtom1010
    Fin15AnchoredAtom1038 Fin15AnchoredAtom1627 Fin15AnchoredAtom3343 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08802
  ] at hbad
  tauto

theorem fin15Anchored_clause22564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom0988 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom3344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16994
  ] at hbad
  tauto

theorem fin15Anchored_clause22565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom3344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16994
  ] at hbad
  tauto

theorem fin15Anchored_clause22566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom3344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16994
  ] at hbad
  tauto

theorem fin15Anchored_clause22567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom3344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16994
  ] at hbad
  tauto

theorem fin15Anchored_clause22568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom3344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16994
  ] at hbad
  tauto

theorem fin15Anchored_clause22569 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom0988 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0988 Fin15AnchoredAtom0993 Fin15AnchoredAtom1011
    Fin15AnchoredAtom1039 Fin15AnchoredAtom1628 Fin15AnchoredAtom3344 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16994
  ] at hbad
  tauto

theorem fin15Anchored_clause22570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3345 chi ∧
      ¬Fin15AnchoredAtom0990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0990 Fin15AnchoredAtom3345 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03170
  ] at hbad
  tauto

theorem fin15Anchored_clause22571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3345 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1040 Fin15AnchoredAtom3345 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03170
  ] at hbad
  tauto

theorem fin15Anchored_clause22572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3345 chi ∧
      ¬Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1629 Fin15AnchoredAtom3345 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03170
  ] at hbad
  tauto

theorem fin15Anchored_clause22573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom3346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05218
  ] at hbad
  tauto

theorem fin15Anchored_clause22574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom3346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05218
  ] at hbad
  tauto

theorem fin15Anchored_clause22575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom3346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05218
  ] at hbad
  tauto

theorem fin15Anchored_clause22576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom3346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05218
  ] at hbad
  tauto

theorem fin15Anchored_clause22577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom3346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05218
  ] at hbad
  tauto

theorem fin15Anchored_clause22578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom0991 Fin15AnchoredAtom1013
    Fin15AnchoredAtom1041 Fin15AnchoredAtom1630 Fin15AnchoredAtom3346 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05218
  ] at hbad
  tauto

theorem fin15Anchored_clause22579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom3347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09314
  ] at hbad
  tauto

theorem fin15Anchored_clause22580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom3347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09314
  ] at hbad
  tauto

theorem fin15Anchored_clause22581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom3347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09314
  ] at hbad
  tauto

theorem fin15Anchored_clause22582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom3347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09314
  ] at hbad
  tauto

theorem fin15Anchored_clause22583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom3347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09314
  ] at hbad
  tauto

theorem fin15Anchored_clause22584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom0992 Fin15AnchoredAtom1014
    Fin15AnchoredAtom1042 Fin15AnchoredAtom1631 Fin15AnchoredAtom3347 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09314
  ] at hbad
  tauto

theorem fin15Anchored_clause22585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom0989 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom3348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17506
  ] at hbad
  tauto

theorem fin15Anchored_clause22586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom3348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17506
  ] at hbad
  tauto

theorem fin15Anchored_clause22587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom3348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17506
  ] at hbad
  tauto

theorem fin15Anchored_clause22588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom3348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17506
  ] at hbad
  tauto

theorem fin15Anchored_clause22589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom3348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17506
  ] at hbad
  tauto

theorem fin15Anchored_clause22590 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom0989 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0989 Fin15AnchoredAtom0993 Fin15AnchoredAtom1015
    Fin15AnchoredAtom1043 Fin15AnchoredAtom1632 Fin15AnchoredAtom3348 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17506
  ] at hbad
  tauto

theorem fin15Anchored_clause22591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3349 chi ∧
      ¬Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1633 Fin15AnchoredAtom3349 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06242
  ] at hbad
  tauto

theorem fin15Anchored_clause22592 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3349 chi ∧
      Fin15AnchoredAtom0990 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom1016 chi ∧
      Fin15AnchoredAtom1044 chi ∧
      Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0990 Fin15AnchoredAtom0991 Fin15AnchoredAtom1016
    Fin15AnchoredAtom1044 Fin15AnchoredAtom1633 Fin15AnchoredAtom3349 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06242
  ] at hbad
  tauto

theorem fin15Anchored_clause22593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom3352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12386
  ] at hbad
  tauto

theorem fin15Anchored_clause22594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom3352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12386
  ] at hbad
  tauto

theorem fin15Anchored_clause22595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom3352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12386
  ] at hbad
  tauto

theorem fin15Anchored_clause22596 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom3352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12386
  ] at hbad
  tauto

theorem fin15Anchored_clause22597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom3352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12386
  ] at hbad
  tauto

theorem fin15Anchored_clause22598 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom0992 Fin15AnchoredAtom1019
    Fin15AnchoredAtom1047 Fin15AnchoredAtom1636 Fin15AnchoredAtom3352 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12386
  ] at hbad
  tauto

theorem fin15Anchored_clause22599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom0991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom3353 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20578
  ] at hbad
  tauto

theorem fin15Anchored_clause22600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom3353 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20578
  ] at hbad
  tauto

theorem fin15Anchored_clause22601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom3353 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20578
  ] at hbad
  tauto

theorem fin15Anchored_clause22602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom3353 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20578
  ] at hbad
  tauto

theorem fin15Anchored_clause22603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom3353 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20578
  ] at hbad
  tauto

theorem fin15Anchored_clause22604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom0991 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0991 Fin15AnchoredAtom0993 Fin15AnchoredAtom1020
    Fin15AnchoredAtom1048 Fin15AnchoredAtom1637 Fin15AnchoredAtom3353 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20578
  ] at hbad
  tauto

theorem fin15Anchored_clause22605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom0992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom3354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24674
  ] at hbad
  tauto

theorem fin15Anchored_clause22606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom0993 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0993 Fin15AnchoredAtom3354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24674
  ] at hbad
  tauto

theorem fin15Anchored_clause22607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom3354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24674
  ] at hbad
  tauto

theorem fin15Anchored_clause22608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom3354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24674
  ] at hbad
  tauto

theorem fin15Anchored_clause22609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom3354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24674
  ] at hbad
  tauto

theorem fin15Anchored_clause22610 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom0992 chi ∧
      Fin15AnchoredAtom0993 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0992 Fin15AnchoredAtom0993 Fin15AnchoredAtom1021
    Fin15AnchoredAtom1049 Fin15AnchoredAtom1638 Fin15AnchoredAtom3354 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24674
  ] at hbad
  tauto

theorem fin15Anchored_clause22611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom3355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00930
  ] at hbad
  tauto

theorem fin15Anchored_clause22612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom3355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00930
  ] at hbad
  tauto

theorem fin15Anchored_clause22613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom3355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00930
  ] at hbad
  tauto

theorem fin15Anchored_clause22614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom3355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00930
  ] at hbad
  tauto

theorem fin15Anchored_clause22615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3355 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom3355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00930
  ] at hbad
  tauto

theorem fin15Anchored_clause22616 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3355 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom0995 Fin15AnchoredAtom1001
    Fin15AnchoredAtom1050 Fin15AnchoredAtom1639 Fin15AnchoredAtom3355 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00930
  ] at hbad
  tauto

theorem fin15Anchored_clause22617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom3356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01442
  ] at hbad
  tauto

theorem fin15Anchored_clause22618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom3356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01442
  ] at hbad
  tauto

theorem fin15Anchored_clause22619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom3356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01442
  ] at hbad
  tauto

theorem fin15Anchored_clause22620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom3356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01442
  ] at hbad
  tauto

theorem fin15Anchored_clause22621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3356 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom3356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01442
  ] at hbad
  tauto

theorem fin15Anchored_clause22622 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3356 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom0996 Fin15AnchoredAtom1002
    Fin15AnchoredAtom1051 Fin15AnchoredAtom1640 Fin15AnchoredAtom3356 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01442
  ] at hbad
  tauto

theorem fin15Anchored_clause22623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom3358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04514
  ] at hbad
  tauto

theorem fin15Anchored_clause22624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom3358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04514
  ] at hbad
  tauto

theorem fin15Anchored_clause22625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom3358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04514
  ] at hbad
  tauto

theorem fin15Anchored_clause22626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3358 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom3358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04514
  ] at hbad
  tauto

theorem fin15Anchored_clause22627 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3358 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom0998 Fin15AnchoredAtom1004
    Fin15AnchoredAtom1053 Fin15AnchoredAtom1642 Fin15AnchoredAtom3358 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04514
  ] at hbad
  tauto

theorem fin15Anchored_clause22628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom3359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08610
  ] at hbad
  tauto

theorem fin15Anchored_clause22629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom3359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08610
  ] at hbad
  tauto

theorem fin15Anchored_clause22630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom3359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08610
  ] at hbad
  tauto

theorem fin15Anchored_clause22631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom3359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08610
  ] at hbad
  tauto

theorem fin15Anchored_clause22632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3359 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom3359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08610
  ] at hbad
  tauto

theorem fin15Anchored_clause22633 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3359 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom0999 Fin15AnchoredAtom1005
    Fin15AnchoredAtom1054 Fin15AnchoredAtom1643 Fin15AnchoredAtom3359 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08610
  ] at hbad
  tauto

theorem fin15Anchored_clause22634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom0994 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom3360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16802
  ] at hbad
  tauto

theorem fin15Anchored_clause22635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom3360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16802
  ] at hbad
  tauto

theorem fin15Anchored_clause22636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1006 Fin15AnchoredAtom3360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16802
  ] at hbad
  tauto

theorem fin15Anchored_clause22637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3360 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1644 Fin15AnchoredAtom3360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16802
  ] at hbad
  tauto

theorem fin15Anchored_clause22638 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3360 chi ∧
      Fin15AnchoredAtom0994 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0994 Fin15AnchoredAtom1000 Fin15AnchoredAtom1006
    Fin15AnchoredAtom1055 Fin15AnchoredAtom1644 Fin15AnchoredAtom3360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16802
  ] at hbad
  tauto

theorem fin15Anchored_clause22639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom3361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01698
  ] at hbad
  tauto

theorem fin15Anchored_clause22640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom3361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01698
  ] at hbad
  tauto

theorem fin15Anchored_clause22641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom3361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01698
  ] at hbad
  tauto

theorem fin15Anchored_clause22642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom3361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01698
  ] at hbad
  tauto

theorem fin15Anchored_clause22643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom3361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01698
  ] at hbad
  tauto

theorem fin15Anchored_clause22644 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom0996 Fin15AnchoredAtom1007
    Fin15AnchoredAtom1056 Fin15AnchoredAtom1645 Fin15AnchoredAtom3361 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01698
  ] at hbad
  tauto

theorem fin15Anchored_clause22645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3362 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom3362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02722
  ] at hbad
  tauto

theorem fin15Anchored_clause22646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3362 chi ∧
      ¬Fin15AnchoredAtom1057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1057 Fin15AnchoredAtom3362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02722
  ] at hbad
  tauto

theorem fin15Anchored_clause22647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom3363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04770
  ] at hbad
  tauto

theorem fin15Anchored_clause22648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom3363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04770
  ] at hbad
  tauto

theorem fin15Anchored_clause22649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom3363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04770
  ] at hbad
  tauto

theorem fin15Anchored_clause22650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom3363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04770
  ] at hbad
  tauto

theorem fin15Anchored_clause22651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom3363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04770
  ] at hbad
  tauto

theorem fin15Anchored_clause22652 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom0998 Fin15AnchoredAtom1009
    Fin15AnchoredAtom1058 Fin15AnchoredAtom1647 Fin15AnchoredAtom3363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04770
  ] at hbad
  tauto

theorem fin15Anchored_clause22653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom3364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08866
  ] at hbad
  tauto

theorem fin15Anchored_clause22654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom3364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08866
  ] at hbad
  tauto

theorem fin15Anchored_clause22655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom3364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08866
  ] at hbad
  tauto

end ErdosSzekeres

end
