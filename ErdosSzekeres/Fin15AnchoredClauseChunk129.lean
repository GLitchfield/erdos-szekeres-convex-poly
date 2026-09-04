module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 129. -/

theorem fin15Anchored_clause16512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom2036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01603
  ] at hbad
  tauto

theorem fin15Anchored_clause16513 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2036 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom0501 Fin15AnchoredAtom0519
    Fin15AnchoredAtom0749 Fin15AnchoredAtom1035 Fin15AnchoredAtom2036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01603
  ] at hbad
  tauto

theorem fin15Anchored_clause16514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2037 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom2037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02627
  ] at hbad
  tauto

theorem fin15Anchored_clause16515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2037 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02627
  ] at hbad
  tauto

theorem fin15Anchored_clause16516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom2038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04675
  ] at hbad
  tauto

theorem fin15Anchored_clause16517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom2038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04675
  ] at hbad
  tauto

theorem fin15Anchored_clause16518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom2038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04675
  ] at hbad
  tauto

theorem fin15Anchored_clause16519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04675
  ] at hbad
  tauto

theorem fin15Anchored_clause16520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom2038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04675
  ] at hbad
  tauto

theorem fin15Anchored_clause16521 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2038 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom0503 Fin15AnchoredAtom0521
    Fin15AnchoredAtom0751 Fin15AnchoredAtom1037 Fin15AnchoredAtom2038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04675
  ] at hbad
  tauto

theorem fin15Anchored_clause16522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom2039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08771
  ] at hbad
  tauto

theorem fin15Anchored_clause16523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom2039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08771
  ] at hbad
  tauto

theorem fin15Anchored_clause16524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom2039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08771
  ] at hbad
  tauto

theorem fin15Anchored_clause16525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08771
  ] at hbad
  tauto

theorem fin15Anchored_clause16526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom2039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08771
  ] at hbad
  tauto

theorem fin15Anchored_clause16527 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2039 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom0504 Fin15AnchoredAtom0522
    Fin15AnchoredAtom0752 Fin15AnchoredAtom1038 Fin15AnchoredAtom2039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08771
  ] at hbad
  tauto

theorem fin15Anchored_clause16528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom2040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16963
  ] at hbad
  tauto

theorem fin15Anchored_clause16529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom2040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16963
  ] at hbad
  tauto

theorem fin15Anchored_clause16530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom2040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16963
  ] at hbad
  tauto

theorem fin15Anchored_clause16531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16963
  ] at hbad
  tauto

theorem fin15Anchored_clause16532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom2040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16963
  ] at hbad
  tauto

theorem fin15Anchored_clause16533 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2040 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom0505 Fin15AnchoredAtom0523
    Fin15AnchoredAtom0753 Fin15AnchoredAtom1039 Fin15AnchoredAtom2040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16963
  ] at hbad
  tauto

theorem fin15Anchored_clause16534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom2041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03139
  ] at hbad
  tauto

theorem fin15Anchored_clause16535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom0502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0502 Fin15AnchoredAtom2041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03139
  ] at hbad
  tauto

theorem fin15Anchored_clause16536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom0524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0524 Fin15AnchoredAtom2041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03139
  ] at hbad
  tauto

theorem fin15Anchored_clause16537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom2041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03139
  ] at hbad
  tauto

theorem fin15Anchored_clause16538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2041 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1040 Fin15AnchoredAtom2041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03139
  ] at hbad
  tauto

theorem fin15Anchored_clause16539 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2041 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0502 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom0502 Fin15AnchoredAtom0524
    Fin15AnchoredAtom0754 Fin15AnchoredAtom1040 Fin15AnchoredAtom2041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03139
  ] at hbad
  tauto

theorem fin15Anchored_clause16540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom2042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05187
  ] at hbad
  tauto

theorem fin15Anchored_clause16541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom2042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05187
  ] at hbad
  tauto

theorem fin15Anchored_clause16542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom2042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05187
  ] at hbad
  tauto

theorem fin15Anchored_clause16543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05187
  ] at hbad
  tauto

theorem fin15Anchored_clause16544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom2042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05187
  ] at hbad
  tauto

theorem fin15Anchored_clause16545 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2042 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom0503 Fin15AnchoredAtom0525
    Fin15AnchoredAtom0755 Fin15AnchoredAtom1041 Fin15AnchoredAtom2042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05187
  ] at hbad
  tauto

theorem fin15Anchored_clause16546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom2043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09283
  ] at hbad
  tauto

theorem fin15Anchored_clause16547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom2043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09283
  ] at hbad
  tauto

theorem fin15Anchored_clause16548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom2043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09283
  ] at hbad
  tauto

theorem fin15Anchored_clause16549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09283
  ] at hbad
  tauto

theorem fin15Anchored_clause16550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom2043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09283
  ] at hbad
  tauto

theorem fin15Anchored_clause16551 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2043 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom0504 Fin15AnchoredAtom0526
    Fin15AnchoredAtom0756 Fin15AnchoredAtom1042 Fin15AnchoredAtom2043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09283
  ] at hbad
  tauto

theorem fin15Anchored_clause16552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom2044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17475
  ] at hbad
  tauto

theorem fin15Anchored_clause16553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom2044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17475
  ] at hbad
  tauto

theorem fin15Anchored_clause16554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom2044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17475
  ] at hbad
  tauto

theorem fin15Anchored_clause16555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17475
  ] at hbad
  tauto

theorem fin15Anchored_clause16556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom2044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17475
  ] at hbad
  tauto

theorem fin15Anchored_clause16557 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2044 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom0505 Fin15AnchoredAtom0527
    Fin15AnchoredAtom0757 Fin15AnchoredAtom1043 Fin15AnchoredAtom2044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17475
  ] at hbad
  tauto

theorem fin15Anchored_clause16558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom0502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0502 Fin15AnchoredAtom2045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06211
  ] at hbad
  tauto

theorem fin15Anchored_clause16559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom2045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06211
  ] at hbad
  tauto

theorem fin15Anchored_clause16560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom0528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0528 Fin15AnchoredAtom2045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06211
  ] at hbad
  tauto

theorem fin15Anchored_clause16561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2045 chi ∧
      ¬Fin15AnchoredAtom0758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0758 Fin15AnchoredAtom2045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06211
  ] at hbad
  tauto

theorem fin15Anchored_clause16562 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2045 chi ∧
      Fin15AnchoredAtom0502 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0502 Fin15AnchoredAtom0503 Fin15AnchoredAtom0528
    Fin15AnchoredAtom0758 Fin15AnchoredAtom1044 Fin15AnchoredAtom2045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06211
  ] at hbad
  tauto

theorem fin15Anchored_clause16563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2046 chi ∧
      ¬Fin15AnchoredAtom0502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0502 Fin15AnchoredAtom2046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10307
  ] at hbad
  tauto

theorem fin15Anchored_clause16564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2046 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom2046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10307
  ] at hbad
  tauto

theorem fin15Anchored_clause16565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2047 chi ∧
      ¬Fin15AnchoredAtom0502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0502 Fin15AnchoredAtom2047 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18499
  ] at hbad
  tauto

theorem fin15Anchored_clause16566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2047 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom2047 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18499
  ] at hbad
  tauto

theorem fin15Anchored_clause16567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom2048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12355
  ] at hbad
  tauto

theorem fin15Anchored_clause16568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom2048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12355
  ] at hbad
  tauto

theorem fin15Anchored_clause16569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom2048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12355
  ] at hbad
  tauto

theorem fin15Anchored_clause16570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12355
  ] at hbad
  tauto

theorem fin15Anchored_clause16571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom2048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12355
  ] at hbad
  tauto

theorem fin15Anchored_clause16572 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2048 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom0504 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0761 Fin15AnchoredAtom1047 Fin15AnchoredAtom2048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12355
  ] at hbad
  tauto

theorem fin15Anchored_clause16573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom2049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20547
  ] at hbad
  tauto

theorem fin15Anchored_clause16574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom2049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20547
  ] at hbad
  tauto

theorem fin15Anchored_clause16575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom2049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20547
  ] at hbad
  tauto

theorem fin15Anchored_clause16576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20547
  ] at hbad
  tauto

theorem fin15Anchored_clause16577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom2049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20547
  ] at hbad
  tauto

theorem fin15Anchored_clause16578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2049 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom0505 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0762 Fin15AnchoredAtom1048 Fin15AnchoredAtom2049 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20547
  ] at hbad
  tauto

theorem fin15Anchored_clause16579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom2050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24643
  ] at hbad
  tauto

theorem fin15Anchored_clause16580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom0505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0505 Fin15AnchoredAtom2050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24643
  ] at hbad
  tauto

theorem fin15Anchored_clause16581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom2050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24643
  ] at hbad
  tauto

theorem fin15Anchored_clause16582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24643
  ] at hbad
  tauto

theorem fin15Anchored_clause16583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom2050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24643
  ] at hbad
  tauto

theorem fin15Anchored_clause16584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2050 chi ∧
      Fin15AnchoredAtom0504 chi ∧
      Fin15AnchoredAtom0505 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom0505 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0763 Fin15AnchoredAtom1049 Fin15AnchoredAtom2050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24643
  ] at hbad
  tauto

theorem fin15Anchored_clause16585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom2051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00899
  ] at hbad
  tauto

theorem fin15Anchored_clause16586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom2051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00899
  ] at hbad
  tauto

theorem fin15Anchored_clause16587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom2051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00899
  ] at hbad
  tauto

theorem fin15Anchored_clause16588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom2051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00899
  ] at hbad
  tauto

theorem fin15Anchored_clause16589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2051 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom2051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00899
  ] at hbad
  tauto

theorem fin15Anchored_clause16590 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2051 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom0507 Fin15AnchoredAtom0513
    Fin15AnchoredAtom0764 Fin15AnchoredAtom1050 Fin15AnchoredAtom2051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00899
  ] at hbad
  tauto

theorem fin15Anchored_clause16591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom2052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01411
  ] at hbad
  tauto

theorem fin15Anchored_clause16592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom2052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01411
  ] at hbad
  tauto

theorem fin15Anchored_clause16593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom2052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01411
  ] at hbad
  tauto

theorem fin15Anchored_clause16594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom2052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01411
  ] at hbad
  tauto

theorem fin15Anchored_clause16595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2052 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom2052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01411
  ] at hbad
  tauto

theorem fin15Anchored_clause16596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2052 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom0508 Fin15AnchoredAtom0514
    Fin15AnchoredAtom0765 Fin15AnchoredAtom1051 Fin15AnchoredAtom2052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01411
  ] at hbad
  tauto

theorem fin15Anchored_clause16597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom2054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04483
  ] at hbad
  tauto

theorem fin15Anchored_clause16598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom2054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04483
  ] at hbad
  tauto

theorem fin15Anchored_clause16599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom2054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04483
  ] at hbad
  tauto

theorem fin15Anchored_clause16600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom2054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04483
  ] at hbad
  tauto

theorem fin15Anchored_clause16601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2054 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom2054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04483
  ] at hbad
  tauto

theorem fin15Anchored_clause16602 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2054 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom0510 Fin15AnchoredAtom0516
    Fin15AnchoredAtom0767 Fin15AnchoredAtom1053 Fin15AnchoredAtom2054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04483
  ] at hbad
  tauto

theorem fin15Anchored_clause16603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom2055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08579
  ] at hbad
  tauto

theorem fin15Anchored_clause16604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom2055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08579
  ] at hbad
  tauto

theorem fin15Anchored_clause16605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0517 Fin15AnchoredAtom2055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08579
  ] at hbad
  tauto

theorem fin15Anchored_clause16606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0768 Fin15AnchoredAtom2055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08579
  ] at hbad
  tauto

theorem fin15Anchored_clause16607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2055 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom2055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08579
  ] at hbad
  tauto

theorem fin15Anchored_clause16608 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2055 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom0511 Fin15AnchoredAtom0517
    Fin15AnchoredAtom0768 Fin15AnchoredAtom1054 Fin15AnchoredAtom2055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08579
  ] at hbad
  tauto

theorem fin15Anchored_clause16609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom2056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16771
  ] at hbad
  tauto

theorem fin15Anchored_clause16610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom2056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16771
  ] at hbad
  tauto

theorem fin15Anchored_clause16611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom0518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0518 Fin15AnchoredAtom2056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16771
  ] at hbad
  tauto

theorem fin15Anchored_clause16612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0769 Fin15AnchoredAtom2056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16771
  ] at hbad
  tauto

theorem fin15Anchored_clause16613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2056 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1055 Fin15AnchoredAtom2056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16771
  ] at hbad
  tauto

theorem fin15Anchored_clause16614 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2056 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom0512 Fin15AnchoredAtom0518
    Fin15AnchoredAtom0769 Fin15AnchoredAtom1055 Fin15AnchoredAtom2056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16771
  ] at hbad
  tauto

theorem fin15Anchored_clause16615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom2057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01667
  ] at hbad
  tauto

theorem fin15Anchored_clause16616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom2057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01667
  ] at hbad
  tauto

theorem fin15Anchored_clause16617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom2057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01667
  ] at hbad
  tauto

theorem fin15Anchored_clause16618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01667
  ] at hbad
  tauto

theorem fin15Anchored_clause16619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom2057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01667
  ] at hbad
  tauto

theorem fin15Anchored_clause16620 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2057 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom0508 Fin15AnchoredAtom0519
    Fin15AnchoredAtom0770 Fin15AnchoredAtom1056 Fin15AnchoredAtom2057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01667
  ] at hbad
  tauto

theorem fin15Anchored_clause16621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom2058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02691
  ] at hbad
  tauto

theorem fin15Anchored_clause16622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2058 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom2058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02691
  ] at hbad
  tauto

theorem fin15Anchored_clause16623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom2059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04739
  ] at hbad
  tauto

theorem fin15Anchored_clause16624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom2059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04739
  ] at hbad
  tauto

theorem fin15Anchored_clause16625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom2059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04739
  ] at hbad
  tauto

theorem fin15Anchored_clause16626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04739
  ] at hbad
  tauto

theorem fin15Anchored_clause16627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom2059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04739
  ] at hbad
  tauto

theorem fin15Anchored_clause16628 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2059 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom0510 Fin15AnchoredAtom0521
    Fin15AnchoredAtom0772 Fin15AnchoredAtom1058 Fin15AnchoredAtom2059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04739
  ] at hbad
  tauto

theorem fin15Anchored_clause16629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom2060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08835
  ] at hbad
  tauto

theorem fin15Anchored_clause16630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom2060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08835
  ] at hbad
  tauto

theorem fin15Anchored_clause16631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom2060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08835
  ] at hbad
  tauto

theorem fin15Anchored_clause16632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08835
  ] at hbad
  tauto

theorem fin15Anchored_clause16633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom2060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08835
  ] at hbad
  tauto

theorem fin15Anchored_clause16634 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2060 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom0511 Fin15AnchoredAtom0522
    Fin15AnchoredAtom0773 Fin15AnchoredAtom1059 Fin15AnchoredAtom2060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08835
  ] at hbad
  tauto

theorem fin15Anchored_clause16635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom2061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17027
  ] at hbad
  tauto

theorem fin15Anchored_clause16636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom2061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17027
  ] at hbad
  tauto

theorem fin15Anchored_clause16637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom2061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17027
  ] at hbad
  tauto

theorem fin15Anchored_clause16638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17027
  ] at hbad
  tauto

theorem fin15Anchored_clause16639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom2061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17027
  ] at hbad
  tauto

end ErdosSzekeres

end
