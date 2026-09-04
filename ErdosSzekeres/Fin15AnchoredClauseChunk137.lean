module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 137. -/

theorem fin15Anchored_clause17536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom2245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01221
  ] at hbad
  tauto

theorem fin15Anchored_clause17537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01221
  ] at hbad
  tauto

theorem fin15Anchored_clause17538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom2245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01221
  ] at hbad
  tauto

theorem fin15Anchored_clause17539 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom0567 Fin15AnchoredAtom0574
    Fin15AnchoredAtom0738 Fin15AnchoredAtom1244 Fin15AnchoredAtom2245 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01221
  ] at hbad
  tauto

theorem fin15Anchored_clause17540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2246 chi ∧
      ¬Fin15AnchoredAtom0568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0568 Fin15AnchoredAtom2246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02245
  ] at hbad
  tauto

theorem fin15Anchored_clause17541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2246 chi ∧
      ¬Fin15AnchoredAtom0575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0575 Fin15AnchoredAtom2246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02245
  ] at hbad
  tauto

theorem fin15Anchored_clause17542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2246 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom2246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02245
  ] at hbad
  tauto

theorem fin15Anchored_clause17543 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2246 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0575 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom0568 Fin15AnchoredAtom0575
    Fin15AnchoredAtom0739 Fin15AnchoredAtom1245 Fin15AnchoredAtom2246 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02245
  ] at hbad
  tauto

theorem fin15Anchored_clause17544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom2247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04293
  ] at hbad
  tauto

theorem fin15Anchored_clause17545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04293
  ] at hbad
  tauto

theorem fin15Anchored_clause17546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04293
  ] at hbad
  tauto

theorem fin15Anchored_clause17547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04293
  ] at hbad
  tauto

theorem fin15Anchored_clause17548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom2247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04293
  ] at hbad
  tauto

theorem fin15Anchored_clause17549 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom0569 Fin15AnchoredAtom0576
    Fin15AnchoredAtom0740 Fin15AnchoredAtom1246 Fin15AnchoredAtom2247 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04293
  ] at hbad
  tauto

theorem fin15Anchored_clause17550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom2248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08389
  ] at hbad
  tauto

theorem fin15Anchored_clause17551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08389
  ] at hbad
  tauto

theorem fin15Anchored_clause17552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08389
  ] at hbad
  tauto

theorem fin15Anchored_clause17553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08389
  ] at hbad
  tauto

theorem fin15Anchored_clause17554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom2248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08389
  ] at hbad
  tauto

theorem fin15Anchored_clause17555 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom0570 Fin15AnchoredAtom0577
    Fin15AnchoredAtom0741 Fin15AnchoredAtom1247 Fin15AnchoredAtom2248 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08389
  ] at hbad
  tauto

theorem fin15Anchored_clause17556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom0564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom2249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16581
  ] at hbad
  tauto

theorem fin15Anchored_clause17557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom2249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16581
  ] at hbad
  tauto

theorem fin15Anchored_clause17558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16581
  ] at hbad
  tauto

theorem fin15Anchored_clause17559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16581
  ] at hbad
  tauto

theorem fin15Anchored_clause17560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom2249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16581
  ] at hbad
  tauto

theorem fin15Anchored_clause17561 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom0564 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0564 Fin15AnchoredAtom0571 Fin15AnchoredAtom0578
    Fin15AnchoredAtom0742 Fin15AnchoredAtom1248 Fin15AnchoredAtom2249 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16581
  ] at hbad
  tauto

theorem fin15Anchored_clause17562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2250 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00837
  ] at hbad
  tauto

theorem fin15Anchored_clause17563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2250 chi ∧
      ¬Fin15AnchoredAtom0579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0579 Fin15AnchoredAtom2250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00837
  ] at hbad
  tauto

theorem fin15Anchored_clause17564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2250 chi ∧
      ¬Fin15AnchoredAtom1249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1249 Fin15AnchoredAtom2250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00837
  ] at hbad
  tauto

theorem fin15Anchored_clause17565 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2250 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0565 Fin15AnchoredAtom0566 Fin15AnchoredAtom0579
    Fin15AnchoredAtom0743 Fin15AnchoredAtom1249 Fin15AnchoredAtom2250 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00837
  ] at hbad
  tauto

theorem fin15Anchored_clause17566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2251 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2251 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01349
  ] at hbad
  tauto

theorem fin15Anchored_clause17567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2251 chi ∧
      ¬Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1250 Fin15AnchoredAtom2251 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01349
  ] at hbad
  tauto

theorem fin15Anchored_clause17568 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2251 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0565 Fin15AnchoredAtom0567 Fin15AnchoredAtom0580
    Fin15AnchoredAtom0744 Fin15AnchoredAtom1250 Fin15AnchoredAtom2251 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01349
  ] at hbad
  tauto

theorem fin15Anchored_clause17569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2253 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2253 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04421
  ] at hbad
  tauto

theorem fin15Anchored_clause17570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2253 chi ∧
      ¬Fin15AnchoredAtom1252 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1252 Fin15AnchoredAtom2253 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04421
  ] at hbad
  tauto

theorem fin15Anchored_clause17571 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2253 chi ∧
      Fin15AnchoredAtom0565 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1252 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0565 Fin15AnchoredAtom0569 Fin15AnchoredAtom0582
    Fin15AnchoredAtom0746 Fin15AnchoredAtom1252 Fin15AnchoredAtom2253 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04421
  ] at hbad
  tauto

theorem fin15Anchored_clause17572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2254 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2254 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08517
  ] at hbad
  tauto

theorem fin15Anchored_clause17573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01605
  ] at hbad
  tauto

theorem fin15Anchored_clause17574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01605
  ] at hbad
  tauto

theorem fin15Anchored_clause17575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom2256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01605
  ] at hbad
  tauto

theorem fin15Anchored_clause17576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01605
  ] at hbad
  tauto

theorem fin15Anchored_clause17577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom2256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01605
  ] at hbad
  tauto

theorem fin15Anchored_clause17578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom0567 Fin15AnchoredAtom0585
    Fin15AnchoredAtom0749 Fin15AnchoredAtom1255 Fin15AnchoredAtom2256 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01605
  ] at hbad
  tauto

theorem fin15Anchored_clause17579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02629
  ] at hbad
  tauto

theorem fin15Anchored_clause17580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom0568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0568 Fin15AnchoredAtom2257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02629
  ] at hbad
  tauto

theorem fin15Anchored_clause17581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom0586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0586 Fin15AnchoredAtom2257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02629
  ] at hbad
  tauto

theorem fin15Anchored_clause17582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02629
  ] at hbad
  tauto

theorem fin15Anchored_clause17583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2257 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom2257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02629
  ] at hbad
  tauto

theorem fin15Anchored_clause17584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2257 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom0568 Fin15AnchoredAtom0586
    Fin15AnchoredAtom0750 Fin15AnchoredAtom1256 Fin15AnchoredAtom2257 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02629
  ] at hbad
  tauto

theorem fin15Anchored_clause17585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04677
  ] at hbad
  tauto

theorem fin15Anchored_clause17586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04677
  ] at hbad
  tauto

theorem fin15Anchored_clause17587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom2258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04677
  ] at hbad
  tauto

theorem fin15Anchored_clause17588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04677
  ] at hbad
  tauto

theorem fin15Anchored_clause17589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom2258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04677
  ] at hbad
  tauto

theorem fin15Anchored_clause17590 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom0569 Fin15AnchoredAtom0587
    Fin15AnchoredAtom0751 Fin15AnchoredAtom1257 Fin15AnchoredAtom2258 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04677
  ] at hbad
  tauto

theorem fin15Anchored_clause17591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08773
  ] at hbad
  tauto

theorem fin15Anchored_clause17592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08773
  ] at hbad
  tauto

theorem fin15Anchored_clause17593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom2259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08773
  ] at hbad
  tauto

theorem fin15Anchored_clause17594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08773
  ] at hbad
  tauto

theorem fin15Anchored_clause17595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom2259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08773
  ] at hbad
  tauto

theorem fin15Anchored_clause17596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom0570 Fin15AnchoredAtom0588
    Fin15AnchoredAtom0752 Fin15AnchoredAtom1258 Fin15AnchoredAtom2259 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08773
  ] at hbad
  tauto

theorem fin15Anchored_clause17597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom0566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom2260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16965
  ] at hbad
  tauto

theorem fin15Anchored_clause17598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom2260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16965
  ] at hbad
  tauto

theorem fin15Anchored_clause17599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom2260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16965
  ] at hbad
  tauto

theorem fin15Anchored_clause17600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16965
  ] at hbad
  tauto

theorem fin15Anchored_clause17601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1259 Fin15AnchoredAtom2260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16965
  ] at hbad
  tauto

theorem fin15Anchored_clause17602 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom0566 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0566 Fin15AnchoredAtom0571 Fin15AnchoredAtom0589
    Fin15AnchoredAtom0753 Fin15AnchoredAtom1259 Fin15AnchoredAtom2260 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16965
  ] at hbad
  tauto

theorem fin15Anchored_clause17603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03141
  ] at hbad
  tauto

theorem fin15Anchored_clause17604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom0590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0590 Fin15AnchoredAtom2261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03141
  ] at hbad
  tauto

theorem fin15Anchored_clause17605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom2261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03141
  ] at hbad
  tauto

theorem fin15Anchored_clause17606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2261 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1260 Fin15AnchoredAtom2261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03141
  ] at hbad
  tauto

theorem fin15Anchored_clause17607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2261 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom0568 Fin15AnchoredAtom0590
    Fin15AnchoredAtom0754 Fin15AnchoredAtom1260 Fin15AnchoredAtom2261 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03141
  ] at hbad
  tauto

theorem fin15Anchored_clause17608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05189
  ] at hbad
  tauto

theorem fin15Anchored_clause17609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05189
  ] at hbad
  tauto

theorem fin15Anchored_clause17610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom2262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05189
  ] at hbad
  tauto

theorem fin15Anchored_clause17611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05189
  ] at hbad
  tauto

theorem fin15Anchored_clause17612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom2262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05189
  ] at hbad
  tauto

theorem fin15Anchored_clause17613 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom0569 Fin15AnchoredAtom0591
    Fin15AnchoredAtom0755 Fin15AnchoredAtom1261 Fin15AnchoredAtom2262 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05189
  ] at hbad
  tauto

theorem fin15Anchored_clause17614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09285
  ] at hbad
  tauto

theorem fin15Anchored_clause17615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09285
  ] at hbad
  tauto

theorem fin15Anchored_clause17616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom2263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09285
  ] at hbad
  tauto

theorem fin15Anchored_clause17617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09285
  ] at hbad
  tauto

theorem fin15Anchored_clause17618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom2263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09285
  ] at hbad
  tauto

theorem fin15Anchored_clause17619 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom0570 Fin15AnchoredAtom0592
    Fin15AnchoredAtom0756 Fin15AnchoredAtom1262 Fin15AnchoredAtom2263 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09285
  ] at hbad
  tauto

theorem fin15Anchored_clause17620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom0567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom2264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17477
  ] at hbad
  tauto

theorem fin15Anchored_clause17621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom2264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17477
  ] at hbad
  tauto

theorem fin15Anchored_clause17622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom2264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17477
  ] at hbad
  tauto

theorem fin15Anchored_clause17623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17477
  ] at hbad
  tauto

theorem fin15Anchored_clause17624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom2264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17477
  ] at hbad
  tauto

theorem fin15Anchored_clause17625 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom0567 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0567 Fin15AnchoredAtom0571 Fin15AnchoredAtom0593
    Fin15AnchoredAtom0757 Fin15AnchoredAtom1263 Fin15AnchoredAtom2264 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17477
  ] at hbad
  tauto

theorem fin15Anchored_clause17626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom0568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0568 Fin15AnchoredAtom2265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06213
  ] at hbad
  tauto

theorem fin15Anchored_clause17627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06213
  ] at hbad
  tauto

theorem fin15Anchored_clause17628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom0594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0594 Fin15AnchoredAtom2265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06213
  ] at hbad
  tauto

theorem fin15Anchored_clause17629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2265 chi ∧
      ¬Fin15AnchoredAtom0758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0758 Fin15AnchoredAtom2265 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06213
  ] at hbad
  tauto

theorem fin15Anchored_clause17630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2266 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2266 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10309
  ] at hbad
  tauto

theorem fin15Anchored_clause17631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2266 chi ∧
      ¬Fin15AnchoredAtom0759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0759 Fin15AnchoredAtom2266 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10309
  ] at hbad
  tauto

theorem fin15Anchored_clause17632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2266 chi ∧
      ¬Fin15AnchoredAtom1265 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1265 Fin15AnchoredAtom2266 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10309
  ] at hbad
  tauto

theorem fin15Anchored_clause17633 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2266 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom1265 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0568 Fin15AnchoredAtom0570 Fin15AnchoredAtom0595
    Fin15AnchoredAtom0759 Fin15AnchoredAtom1265 Fin15AnchoredAtom2266 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10309
  ] at hbad
  tauto

theorem fin15Anchored_clause17634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2267 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom2267 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18501
  ] at hbad
  tauto

theorem fin15Anchored_clause17635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2267 chi ∧
      ¬Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1266 Fin15AnchoredAtom2267 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18501
  ] at hbad
  tauto

theorem fin15Anchored_clause17636 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2267 chi ∧
      Fin15AnchoredAtom0568 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0568 Fin15AnchoredAtom0571 Fin15AnchoredAtom0596
    Fin15AnchoredAtom0760 Fin15AnchoredAtom1266 Fin15AnchoredAtom2267 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18501
  ] at hbad
  tauto

theorem fin15Anchored_clause17637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12357
  ] at hbad
  tauto

theorem fin15Anchored_clause17638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12357
  ] at hbad
  tauto

theorem fin15Anchored_clause17639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom2268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12357
  ] at hbad
  tauto

theorem fin15Anchored_clause17640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12357
  ] at hbad
  tauto

theorem fin15Anchored_clause17641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom2268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12357
  ] at hbad
  tauto

theorem fin15Anchored_clause17642 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom0570 Fin15AnchoredAtom0597
    Fin15AnchoredAtom0761 Fin15AnchoredAtom1267 Fin15AnchoredAtom2268 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12357
  ] at hbad
  tauto

theorem fin15Anchored_clause17643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom0569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom2269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20549
  ] at hbad
  tauto

theorem fin15Anchored_clause17644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom2269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20549
  ] at hbad
  tauto

theorem fin15Anchored_clause17645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom2269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20549
  ] at hbad
  tauto

theorem fin15Anchored_clause17646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20549
  ] at hbad
  tauto

theorem fin15Anchored_clause17647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom2269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20549
  ] at hbad
  tauto

theorem fin15Anchored_clause17648 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom0569 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0569 Fin15AnchoredAtom0571 Fin15AnchoredAtom0598
    Fin15AnchoredAtom0762 Fin15AnchoredAtom1268 Fin15AnchoredAtom2269 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20549
  ] at hbad
  tauto

theorem fin15Anchored_clause17649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom0570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom2270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24645
  ] at hbad
  tauto

theorem fin15Anchored_clause17650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom0571 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0571 Fin15AnchoredAtom2270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24645
  ] at hbad
  tauto

theorem fin15Anchored_clause17651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom2270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24645
  ] at hbad
  tauto

theorem fin15Anchored_clause17652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24645
  ] at hbad
  tauto

theorem fin15Anchored_clause17653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom2270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24645
  ] at hbad
  tauto

theorem fin15Anchored_clause17654 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom0570 chi ∧
      Fin15AnchoredAtom0571 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0570 Fin15AnchoredAtom0571 Fin15AnchoredAtom0599
    Fin15AnchoredAtom0763 Fin15AnchoredAtom1269 Fin15AnchoredAtom2270 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24645
  ] at hbad
  tauto

theorem fin15Anchored_clause17655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2271 chi ∧
      ¬Fin15AnchoredAtom0573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0573 Fin15AnchoredAtom2271 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00901
  ] at hbad
  tauto

theorem fin15Anchored_clause17656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2272 chi ∧
      ¬Fin15AnchoredAtom0572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0572 Fin15AnchoredAtom2272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01413
  ] at hbad
  tauto

theorem fin15Anchored_clause17657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2272 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom2272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01413
  ] at hbad
  tauto

theorem fin15Anchored_clause17658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2272 chi ∧
      ¬Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1271 Fin15AnchoredAtom2272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01413
  ] at hbad
  tauto

theorem fin15Anchored_clause17659 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2272 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0572 Fin15AnchoredAtom0574 Fin15AnchoredAtom0580
    Fin15AnchoredAtom0765 Fin15AnchoredAtom1271 Fin15AnchoredAtom2272 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01413
  ] at hbad
  tauto

theorem fin15Anchored_clause17660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2274 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom2274 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04485
  ] at hbad
  tauto

theorem fin15Anchored_clause17661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2275 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom2275 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08581
  ] at hbad
  tauto

theorem fin15Anchored_clause17662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2276 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom2276 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16773
  ] at hbad
  tauto

theorem fin15Anchored_clause17663 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2276 chi ∧
      Fin15AnchoredAtom0572 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1275 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0572 Fin15AnchoredAtom0578 Fin15AnchoredAtom0584
    Fin15AnchoredAtom0769 Fin15AnchoredAtom1275 Fin15AnchoredAtom2276 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16773
  ] at hbad
  tauto

end ErdosSzekeres

end
