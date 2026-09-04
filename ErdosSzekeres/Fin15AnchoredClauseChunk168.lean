module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 168. -/

theorem fin15Anchored_clause21504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom3110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04650
  ] at hbad
  tauto

theorem fin15Anchored_clause21505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom3110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04650
  ] at hbad
  tauto

theorem fin15Anchored_clause21506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom3110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04650
  ] at hbad
  tauto

theorem fin15Anchored_clause21507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom3110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04650
  ] at hbad
  tauto

theorem fin15Anchored_clause21508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom3110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04650
  ] at hbad
  tauto

theorem fin15Anchored_clause21509 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom0902 Fin15AnchoredAtom0928
    Fin15AnchoredAtom1009 Fin15AnchoredAtom1394 Fin15AnchoredAtom3110 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04650
  ] at hbad
  tauto

theorem fin15Anchored_clause21510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom3111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08746
  ] at hbad
  tauto

theorem fin15Anchored_clause21511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom3111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08746
  ] at hbad
  tauto

theorem fin15Anchored_clause21512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom3111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08746
  ] at hbad
  tauto

theorem fin15Anchored_clause21513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom3111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08746
  ] at hbad
  tauto

theorem fin15Anchored_clause21514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom3111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08746
  ] at hbad
  tauto

theorem fin15Anchored_clause21515 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom0903 Fin15AnchoredAtom0929
    Fin15AnchoredAtom1010 Fin15AnchoredAtom1395 Fin15AnchoredAtom3111 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08746
  ] at hbad
  tauto

theorem fin15Anchored_clause21516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom3112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16938
  ] at hbad
  tauto

theorem fin15Anchored_clause21517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom3112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16938
  ] at hbad
  tauto

theorem fin15Anchored_clause21518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom3112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16938
  ] at hbad
  tauto

theorem fin15Anchored_clause21519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom3112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16938
  ] at hbad
  tauto

theorem fin15Anchored_clause21520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom3112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16938
  ] at hbad
  tauto

theorem fin15Anchored_clause21521 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom0904 Fin15AnchoredAtom0930
    Fin15AnchoredAtom1011 Fin15AnchoredAtom1396 Fin15AnchoredAtom3112 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16938
  ] at hbad
  tauto

theorem fin15Anchored_clause21522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3113 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom3113 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03114
  ] at hbad
  tauto

theorem fin15Anchored_clause21523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3113 chi ∧
      ¬Fin15AnchoredAtom0901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0901 Fin15AnchoredAtom3113 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03114
  ] at hbad
  tauto

theorem fin15Anchored_clause21524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom3114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05162
  ] at hbad
  tauto

theorem fin15Anchored_clause21525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom3114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05162
  ] at hbad
  tauto

theorem fin15Anchored_clause21526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom3114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05162
  ] at hbad
  tauto

theorem fin15Anchored_clause21527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom3114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05162
  ] at hbad
  tauto

theorem fin15Anchored_clause21528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom3114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05162
  ] at hbad
  tauto

theorem fin15Anchored_clause21529 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom0902 Fin15AnchoredAtom0932
    Fin15AnchoredAtom1013 Fin15AnchoredAtom1398 Fin15AnchoredAtom3114 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05162
  ] at hbad
  tauto

theorem fin15Anchored_clause21530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom3115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09258
  ] at hbad
  tauto

theorem fin15Anchored_clause21531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom3115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09258
  ] at hbad
  tauto

theorem fin15Anchored_clause21532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom3115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09258
  ] at hbad
  tauto

theorem fin15Anchored_clause21533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom3115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09258
  ] at hbad
  tauto

theorem fin15Anchored_clause21534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom3115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09258
  ] at hbad
  tauto

theorem fin15Anchored_clause21535 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom0903 Fin15AnchoredAtom0933
    Fin15AnchoredAtom1014 Fin15AnchoredAtom1399 Fin15AnchoredAtom3115 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09258
  ] at hbad
  tauto

theorem fin15Anchored_clause21536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom3116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17450
  ] at hbad
  tauto

theorem fin15Anchored_clause21537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom3116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17450
  ] at hbad
  tauto

theorem fin15Anchored_clause21538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom3116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17450
  ] at hbad
  tauto

theorem fin15Anchored_clause21539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom3116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17450
  ] at hbad
  tauto

theorem fin15Anchored_clause21540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom3116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17450
  ] at hbad
  tauto

theorem fin15Anchored_clause21541 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom0904 Fin15AnchoredAtom0934
    Fin15AnchoredAtom1015 Fin15AnchoredAtom1400 Fin15AnchoredAtom3116 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17450
  ] at hbad
  tauto

theorem fin15Anchored_clause21542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom0901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0901 Fin15AnchoredAtom3117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06186
  ] at hbad
  tauto

theorem fin15Anchored_clause21543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0935 Fin15AnchoredAtom3117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06186
  ] at hbad
  tauto

theorem fin15Anchored_clause21544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom1016 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1016 Fin15AnchoredAtom3117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06186
  ] at hbad
  tauto

theorem fin15Anchored_clause21545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3117 chi ∧
      ¬Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1401 Fin15AnchoredAtom3117 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06186
  ] at hbad
  tauto

theorem fin15Anchored_clause21546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3119 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom3119 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18474
  ] at hbad
  tauto

theorem fin15Anchored_clause21547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom3120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12330
  ] at hbad
  tauto

theorem fin15Anchored_clause21548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom3120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12330
  ] at hbad
  tauto

theorem fin15Anchored_clause21549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom3120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12330
  ] at hbad
  tauto

theorem fin15Anchored_clause21550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom3120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12330
  ] at hbad
  tauto

theorem fin15Anchored_clause21551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom3120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12330
  ] at hbad
  tauto

theorem fin15Anchored_clause21552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom0903 Fin15AnchoredAtom0938
    Fin15AnchoredAtom1019 Fin15AnchoredAtom1404 Fin15AnchoredAtom3120 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12330
  ] at hbad
  tauto

theorem fin15Anchored_clause21553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom3121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20522
  ] at hbad
  tauto

theorem fin15Anchored_clause21554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom3121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20522
  ] at hbad
  tauto

theorem fin15Anchored_clause21555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom3121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20522
  ] at hbad
  tauto

theorem fin15Anchored_clause21556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom3121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20522
  ] at hbad
  tauto

theorem fin15Anchored_clause21557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom3121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20522
  ] at hbad
  tauto

theorem fin15Anchored_clause21558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom0904 Fin15AnchoredAtom0939
    Fin15AnchoredAtom1020 Fin15AnchoredAtom1405 Fin15AnchoredAtom3121 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20522
  ] at hbad
  tauto

theorem fin15Anchored_clause21559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom3122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24618
  ] at hbad
  tauto

theorem fin15Anchored_clause21560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom3122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24618
  ] at hbad
  tauto

theorem fin15Anchored_clause21561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom3122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24618
  ] at hbad
  tauto

theorem fin15Anchored_clause21562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom3122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24618
  ] at hbad
  tauto

theorem fin15Anchored_clause21563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom3122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24618
  ] at hbad
  tauto

theorem fin15Anchored_clause21564 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom0904 Fin15AnchoredAtom0940
    Fin15AnchoredAtom1021 Fin15AnchoredAtom1406 Fin15AnchoredAtom3122 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24618
  ] at hbad
  tauto

theorem fin15Anchored_clause21565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom3123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00458
  ] at hbad
  tauto

theorem fin15Anchored_clause21566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom3123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00458
  ] at hbad
  tauto

theorem fin15Anchored_clause21567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3123 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom3123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00458
  ] at hbad
  tauto

theorem fin15Anchored_clause21568 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom0906 Fin15AnchoredAtom0913
    Fin15AnchoredAtom1022 Fin15AnchoredAtom1407 Fin15AnchoredAtom3123 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00458
  ] at hbad
  tauto

theorem fin15Anchored_clause21569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom3124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00714
  ] at hbad
  tauto

theorem fin15Anchored_clause21570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom3124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00714
  ] at hbad
  tauto

theorem fin15Anchored_clause21571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom3124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00714
  ] at hbad
  tauto

theorem fin15Anchored_clause21572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom3124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00714
  ] at hbad
  tauto

theorem fin15Anchored_clause21573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom3124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00714
  ] at hbad
  tauto

theorem fin15Anchored_clause21574 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom0907 Fin15AnchoredAtom0914
    Fin15AnchoredAtom1023 Fin15AnchoredAtom1408 Fin15AnchoredAtom3124 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00714
  ] at hbad
  tauto

theorem fin15Anchored_clause21575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom3125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01226
  ] at hbad
  tauto

theorem fin15Anchored_clause21576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom3125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01226
  ] at hbad
  tauto

theorem fin15Anchored_clause21577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom3125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01226
  ] at hbad
  tauto

theorem fin15Anchored_clause21578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom3125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01226
  ] at hbad
  tauto

theorem fin15Anchored_clause21579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom3125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01226
  ] at hbad
  tauto

theorem fin15Anchored_clause21580 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom0908 Fin15AnchoredAtom0915
    Fin15AnchoredAtom1024 Fin15AnchoredAtom1409 Fin15AnchoredAtom3125 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01226
  ] at hbad
  tauto

theorem fin15Anchored_clause21581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3126 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom3126 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02250
  ] at hbad
  tauto

theorem fin15Anchored_clause21582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom3127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04298
  ] at hbad
  tauto

theorem fin15Anchored_clause21583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom3127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04298
  ] at hbad
  tauto

theorem fin15Anchored_clause21584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom3127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04298
  ] at hbad
  tauto

theorem fin15Anchored_clause21585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom3127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04298
  ] at hbad
  tauto

theorem fin15Anchored_clause21586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom3127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04298
  ] at hbad
  tauto

theorem fin15Anchored_clause21587 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom0910 Fin15AnchoredAtom0917
    Fin15AnchoredAtom1026 Fin15AnchoredAtom1411 Fin15AnchoredAtom3127 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04298
  ] at hbad
  tauto

theorem fin15Anchored_clause21588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom3128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08394
  ] at hbad
  tauto

theorem fin15Anchored_clause21589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom3128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08394
  ] at hbad
  tauto

theorem fin15Anchored_clause21590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom3128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08394
  ] at hbad
  tauto

theorem fin15Anchored_clause21591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom3128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08394
  ] at hbad
  tauto

theorem fin15Anchored_clause21592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom3128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08394
  ] at hbad
  tauto

theorem fin15Anchored_clause21593 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom0911 Fin15AnchoredAtom0918
    Fin15AnchoredAtom1027 Fin15AnchoredAtom1412 Fin15AnchoredAtom3128 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08394
  ] at hbad
  tauto

theorem fin15Anchored_clause21594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom3129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16586
  ] at hbad
  tauto

theorem fin15Anchored_clause21595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom3129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16586
  ] at hbad
  tauto

theorem fin15Anchored_clause21596 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom3129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16586
  ] at hbad
  tauto

theorem fin15Anchored_clause21597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom3129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16586
  ] at hbad
  tauto

theorem fin15Anchored_clause21598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom3129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16586
  ] at hbad
  tauto

theorem fin15Anchored_clause21599 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom0912 Fin15AnchoredAtom0919
    Fin15AnchoredAtom1028 Fin15AnchoredAtom1413 Fin15AnchoredAtom3129 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16586
  ] at hbad
  tauto

theorem fin15Anchored_clause21600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom3130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00842
  ] at hbad
  tauto

theorem fin15Anchored_clause21601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom3130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00842
  ] at hbad
  tauto

theorem fin15Anchored_clause21602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom3130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00842
  ] at hbad
  tauto

theorem fin15Anchored_clause21603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3130 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom3130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00842
  ] at hbad
  tauto

theorem fin15Anchored_clause21604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom0907 Fin15AnchoredAtom0920
    Fin15AnchoredAtom1029 Fin15AnchoredAtom1414 Fin15AnchoredAtom3130 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00842
  ] at hbad
  tauto

theorem fin15Anchored_clause21605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom3131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01354
  ] at hbad
  tauto

theorem fin15Anchored_clause21606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom3131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01354
  ] at hbad
  tauto

theorem fin15Anchored_clause21607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom3131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01354
  ] at hbad
  tauto

theorem fin15Anchored_clause21608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3131 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom3131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01354
  ] at hbad
  tauto

theorem fin15Anchored_clause21609 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3131 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom0908 Fin15AnchoredAtom0921
    Fin15AnchoredAtom1030 Fin15AnchoredAtom1415 Fin15AnchoredAtom3131 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01354
  ] at hbad
  tauto

theorem fin15Anchored_clause21610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom3133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04426
  ] at hbad
  tauto

theorem fin15Anchored_clause21611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom3133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04426
  ] at hbad
  tauto

theorem fin15Anchored_clause21612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0923 Fin15AnchoredAtom3133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04426
  ] at hbad
  tauto

theorem fin15Anchored_clause21613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom3133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04426
  ] at hbad
  tauto

theorem fin15Anchored_clause21614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3133 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom3133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04426
  ] at hbad
  tauto

theorem fin15Anchored_clause21615 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3133 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom0910 Fin15AnchoredAtom0923
    Fin15AnchoredAtom1032 Fin15AnchoredAtom1417 Fin15AnchoredAtom3133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04426
  ] at hbad
  tauto

theorem fin15Anchored_clause21616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom3134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08522
  ] at hbad
  tauto

theorem fin15Anchored_clause21617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom3134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08522
  ] at hbad
  tauto

theorem fin15Anchored_clause21618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom3134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08522
  ] at hbad
  tauto

theorem fin15Anchored_clause21619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom3134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08522
  ] at hbad
  tauto

theorem fin15Anchored_clause21620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3134 chi ∧
      ¬Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1418 Fin15AnchoredAtom3134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08522
  ] at hbad
  tauto

theorem fin15Anchored_clause21621 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom0911 Fin15AnchoredAtom0924
    Fin15AnchoredAtom1033 Fin15AnchoredAtom1418 Fin15AnchoredAtom3134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08522
  ] at hbad
  tauto

theorem fin15Anchored_clause21622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom3135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16714
  ] at hbad
  tauto

theorem fin15Anchored_clause21623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom3135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16714
  ] at hbad
  tauto

theorem fin15Anchored_clause21624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1034 Fin15AnchoredAtom3135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16714
  ] at hbad
  tauto

theorem fin15Anchored_clause21625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3135 chi ∧
      ¬Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1419 Fin15AnchoredAtom3135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16714
  ] at hbad
  tauto

theorem fin15Anchored_clause21626 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3135 chi ∧
      Fin15AnchoredAtom0906 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0906 Fin15AnchoredAtom0912 Fin15AnchoredAtom0925
    Fin15AnchoredAtom1034 Fin15AnchoredAtom1419 Fin15AnchoredAtom3135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16714
  ] at hbad
  tauto

theorem fin15Anchored_clause21627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom3136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01610
  ] at hbad
  tauto

theorem fin15Anchored_clause21628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom3136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01610
  ] at hbad
  tauto

theorem fin15Anchored_clause21629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom3136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01610
  ] at hbad
  tauto

theorem fin15Anchored_clause21630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom3136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01610
  ] at hbad
  tauto

theorem fin15Anchored_clause21631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom3136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01610
  ] at hbad
  tauto

end ErdosSzekeres

end
