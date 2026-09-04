module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 150. -/

theorem fin15Anchored_clause19200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom2585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17681
  ] at hbad
  tauto

theorem fin15Anchored_clause19201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom2585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17681
  ] at hbad
  tauto

theorem fin15Anchored_clause19202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17681
  ] at hbad
  tauto

theorem fin15Anchored_clause19203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0793 Fin15AnchoredAtom2585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17681
  ] at hbad
  tauto

theorem fin15Anchored_clause19204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2585 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1584 Fin15AnchoredAtom2585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17681
  ] at hbad
  tauto

theorem fin15Anchored_clause19205 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom0684 Fin15AnchoredAtom0693
    Fin15AnchoredAtom0793 Fin15AnchoredAtom1584 Fin15AnchoredAtom2585 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17681
  ] at hbad
  tauto

theorem fin15Anchored_clause19206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom2589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12561
  ] at hbad
  tauto

theorem fin15Anchored_clause19207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom2589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12561
  ] at hbad
  tauto

theorem fin15Anchored_clause19208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12561
  ] at hbad
  tauto

theorem fin15Anchored_clause19209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12561
  ] at hbad
  tauto

theorem fin15Anchored_clause19210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2589 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom2589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12561
  ] at hbad
  tauto

theorem fin15Anchored_clause19211 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom0683 Fin15AnchoredAtom0697
    Fin15AnchoredAtom0797 Fin15AnchoredAtom1588 Fin15AnchoredAtom2589 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12561
  ] at hbad
  tauto

theorem fin15Anchored_clause19212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom2590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20753
  ] at hbad
  tauto

theorem fin15Anchored_clause19213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom2590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20753
  ] at hbad
  tauto

theorem fin15Anchored_clause19214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom2590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20753
  ] at hbad
  tauto

theorem fin15Anchored_clause19215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2590 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0798 Fin15AnchoredAtom2590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20753
  ] at hbad
  tauto

theorem fin15Anchored_clause19216 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom0684 Fin15AnchoredAtom0698
    Fin15AnchoredAtom0798 Fin15AnchoredAtom1589 Fin15AnchoredAtom2590 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20753
  ] at hbad
  tauto

theorem fin15Anchored_clause19217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom2591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24849
  ] at hbad
  tauto

theorem fin15Anchored_clause19218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom2591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24849
  ] at hbad
  tauto

theorem fin15Anchored_clause19219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom2591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24849
  ] at hbad
  tauto

theorem fin15Anchored_clause19220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0799 Fin15AnchoredAtom2591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24849
  ] at hbad
  tauto

theorem fin15Anchored_clause19221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2591 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom2591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24849
  ] at hbad
  tauto

theorem fin15Anchored_clause19222 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom0684 Fin15AnchoredAtom0699
    Fin15AnchoredAtom0799 Fin15AnchoredAtom1590 Fin15AnchoredAtom2591 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24849
  ] at hbad
  tauto

theorem fin15Anchored_clause19223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2592 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03601
  ] at hbad
  tauto

theorem fin15Anchored_clause19224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2592 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03601
  ] at hbad
  tauto

theorem fin15Anchored_clause19225 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2592 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom0686 Fin15AnchoredAtom0690
    Fin15AnchoredAtom0800 Fin15AnchoredAtom1591 Fin15AnchoredAtom2592 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03601
  ] at hbad
  tauto

theorem fin15Anchored_clause19226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05649
  ] at hbad
  tauto

theorem fin15Anchored_clause19227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05649
  ] at hbad
  tauto

theorem fin15Anchored_clause19228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05649
  ] at hbad
  tauto

theorem fin15Anchored_clause19229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05649
  ] at hbad
  tauto

theorem fin15Anchored_clause19230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom2593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05649
  ] at hbad
  tauto

theorem fin15Anchored_clause19231 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom0687 Fin15AnchoredAtom0691
    Fin15AnchoredAtom0801 Fin15AnchoredAtom1592 Fin15AnchoredAtom2593 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05649
  ] at hbad
  tauto

theorem fin15Anchored_clause19232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09745
  ] at hbad
  tauto

theorem fin15Anchored_clause19233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom2594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09745
  ] at hbad
  tauto

theorem fin15Anchored_clause19234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09745
  ] at hbad
  tauto

theorem fin15Anchored_clause19235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09745
  ] at hbad
  tauto

theorem fin15Anchored_clause19236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom2594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09745
  ] at hbad
  tauto

theorem fin15Anchored_clause19237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom0688 Fin15AnchoredAtom0692
    Fin15AnchoredAtom0802 Fin15AnchoredAtom1593 Fin15AnchoredAtom2594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09745
  ] at hbad
  tauto

theorem fin15Anchored_clause19238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17937
  ] at hbad
  tauto

theorem fin15Anchored_clause19239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17937
  ] at hbad
  tauto

theorem fin15Anchored_clause19240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17937
  ] at hbad
  tauto

theorem fin15Anchored_clause19241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17937
  ] at hbad
  tauto

theorem fin15Anchored_clause19242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom2595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17937
  ] at hbad
  tauto

theorem fin15Anchored_clause19243 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom0689 Fin15AnchoredAtom0693
    Fin15AnchoredAtom0803 Fin15AnchoredAtom1594 Fin15AnchoredAtom2595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17937
  ] at hbad
  tauto

theorem fin15Anchored_clause19244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom0686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom2596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06673
  ] at hbad
  tauto

theorem fin15Anchored_clause19245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06673
  ] at hbad
  tauto

theorem fin15Anchored_clause19246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom2596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06673
  ] at hbad
  tauto

theorem fin15Anchored_clause19247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom2596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06673
  ] at hbad
  tauto

theorem fin15Anchored_clause19248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2596 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1595 Fin15AnchoredAtom2596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06673
  ] at hbad
  tauto

theorem fin15Anchored_clause19249 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2596 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom0687 Fin15AnchoredAtom0694
    Fin15AnchoredAtom0804 Fin15AnchoredAtom1595 Fin15AnchoredAtom2596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06673
  ] at hbad
  tauto

theorem fin15Anchored_clause19250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom0686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom2597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10769
  ] at hbad
  tauto

theorem fin15Anchored_clause19251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom0695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0695 Fin15AnchoredAtom2597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10769
  ] at hbad
  tauto

theorem fin15Anchored_clause19252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2597 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom2597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10769
  ] at hbad
  tauto

theorem fin15Anchored_clause19253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2597 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom0688 Fin15AnchoredAtom0695
    Fin15AnchoredAtom0805 Fin15AnchoredAtom1596 Fin15AnchoredAtom2597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10769
  ] at hbad
  tauto

theorem fin15Anchored_clause19254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom0686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom2598 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18961
  ] at hbad
  tauto

theorem fin15Anchored_clause19255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2598 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18961
  ] at hbad
  tauto

theorem fin15Anchored_clause19256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom0696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0696 Fin15AnchoredAtom2598 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18961
  ] at hbad
  tauto

theorem fin15Anchored_clause19257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2598 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0806 Fin15AnchoredAtom2598 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18961
  ] at hbad
  tauto

theorem fin15Anchored_clause19258 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2598 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0696 chi ∧
      Fin15AnchoredAtom0806 chi ∧
      Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom0689 Fin15AnchoredAtom0696
    Fin15AnchoredAtom0806 Fin15AnchoredAtom1597 Fin15AnchoredAtom2598 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18961
  ] at hbad
  tauto

theorem fin15Anchored_clause19259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12817
  ] at hbad
  tauto

theorem fin15Anchored_clause19260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom2599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12817
  ] at hbad
  tauto

theorem fin15Anchored_clause19261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12817
  ] at hbad
  tauto

theorem fin15Anchored_clause19262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12817
  ] at hbad
  tauto

theorem fin15Anchored_clause19263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom2599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12817
  ] at hbad
  tauto

theorem fin15Anchored_clause19264 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom0688 Fin15AnchoredAtom0697
    Fin15AnchoredAtom0807 Fin15AnchoredAtom1598 Fin15AnchoredAtom2599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12817
  ] at hbad
  tauto

theorem fin15Anchored_clause19265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21009
  ] at hbad
  tauto

theorem fin15Anchored_clause19266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21009
  ] at hbad
  tauto

theorem fin15Anchored_clause19267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom2600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21009
  ] at hbad
  tauto

theorem fin15Anchored_clause19268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21009
  ] at hbad
  tauto

theorem fin15Anchored_clause19269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom2600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21009
  ] at hbad
  tauto

theorem fin15Anchored_clause19270 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom0689 Fin15AnchoredAtom0698
    Fin15AnchoredAtom0808 Fin15AnchoredAtom1599 Fin15AnchoredAtom2600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21009
  ] at hbad
  tauto

theorem fin15Anchored_clause19271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom2601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25105
  ] at hbad
  tauto

theorem fin15Anchored_clause19272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25105
  ] at hbad
  tauto

theorem fin15Anchored_clause19273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom2601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25105
  ] at hbad
  tauto

theorem fin15Anchored_clause19274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25105
  ] at hbad
  tauto

theorem fin15Anchored_clause19275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom2601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25105
  ] at hbad
  tauto

theorem fin15Anchored_clause19276 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom0689 Fin15AnchoredAtom0699
    Fin15AnchoredAtom0809 Fin15AnchoredAtom1600 Fin15AnchoredAtom2601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25105
  ] at hbad
  tauto

theorem fin15Anchored_clause19277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom2602 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07185
  ] at hbad
  tauto

theorem fin15Anchored_clause19278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2602 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07185
  ] at hbad
  tauto

theorem fin15Anchored_clause19279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom2602 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07185
  ] at hbad
  tauto

theorem fin15Anchored_clause19280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom2602 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07185
  ] at hbad
  tauto

theorem fin15Anchored_clause19281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2602 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1601 Fin15AnchoredAtom2602 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07185
  ] at hbad
  tauto

theorem fin15Anchored_clause19282 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2602 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom0691 Fin15AnchoredAtom0694
    Fin15AnchoredAtom0810 Fin15AnchoredAtom1601 Fin15AnchoredAtom2602 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07185
  ] at hbad
  tauto

theorem fin15Anchored_clause19283 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom2603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11281
  ] at hbad
  tauto

theorem fin15Anchored_clause19284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11281
  ] at hbad
  tauto

theorem fin15Anchored_clause19285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom0695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0695 Fin15AnchoredAtom2603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11281
  ] at hbad
  tauto

theorem fin15Anchored_clause19286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11281
  ] at hbad
  tauto

theorem fin15Anchored_clause19287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2603 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1602 Fin15AnchoredAtom2603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11281
  ] at hbad
  tauto

theorem fin15Anchored_clause19288 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2603 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom0692 Fin15AnchoredAtom0695
    Fin15AnchoredAtom0811 Fin15AnchoredAtom1602 Fin15AnchoredAtom2603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11281
  ] at hbad
  tauto

theorem fin15Anchored_clause19289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2604 chi ∧
      ¬Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom2604 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19473
  ] at hbad
  tauto

theorem fin15Anchored_clause19290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2604 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2604 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19473
  ] at hbad
  tauto

theorem fin15Anchored_clause19291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2604 chi ∧
      ¬Fin15AnchoredAtom0812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0812 Fin15AnchoredAtom2604 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19473
  ] at hbad
  tauto

theorem fin15Anchored_clause19292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13329
  ] at hbad
  tauto

theorem fin15Anchored_clause19293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13329
  ] at hbad
  tauto

theorem fin15Anchored_clause19294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13329
  ] at hbad
  tauto

theorem fin15Anchored_clause19295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13329
  ] at hbad
  tauto

theorem fin15Anchored_clause19296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom2605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13329
  ] at hbad
  tauto

theorem fin15Anchored_clause19297 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom0692 Fin15AnchoredAtom0697
    Fin15AnchoredAtom0813 Fin15AnchoredAtom1604 Fin15AnchoredAtom2605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13329
  ] at hbad
  tauto

theorem fin15Anchored_clause19298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21521
  ] at hbad
  tauto

theorem fin15Anchored_clause19299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21521
  ] at hbad
  tauto

theorem fin15Anchored_clause19300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom2606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21521
  ] at hbad
  tauto

theorem fin15Anchored_clause19301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21521
  ] at hbad
  tauto

theorem fin15Anchored_clause19302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom2606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21521
  ] at hbad
  tauto

theorem fin15Anchored_clause19303 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom0693 Fin15AnchoredAtom0698
    Fin15AnchoredAtom0814 Fin15AnchoredAtom1605 Fin15AnchoredAtom2606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21521
  ] at hbad
  tauto

theorem fin15Anchored_clause19304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25617
  ] at hbad
  tauto

theorem fin15Anchored_clause19305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25617
  ] at hbad
  tauto

theorem fin15Anchored_clause19306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom2607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25617
  ] at hbad
  tauto

theorem fin15Anchored_clause19307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25617
  ] at hbad
  tauto

theorem fin15Anchored_clause19308 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom2607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25617
  ] at hbad
  tauto

theorem fin15Anchored_clause19309 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom0693 Fin15AnchoredAtom0699
    Fin15AnchoredAtom0815 Fin15AnchoredAtom1606 Fin15AnchoredAtom2607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25617
  ] at hbad
  tauto

theorem fin15Anchored_clause19310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom2608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14353
  ] at hbad
  tauto

theorem fin15Anchored_clause19311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom0695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0695 Fin15AnchoredAtom2608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14353
  ] at hbad
  tauto

theorem fin15Anchored_clause19312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14353
  ] at hbad
  tauto

theorem fin15Anchored_clause19313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0816 Fin15AnchoredAtom2608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14353
  ] at hbad
  tauto

theorem fin15Anchored_clause19314 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2608 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1607 Fin15AnchoredAtom2608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14353
  ] at hbad
  tauto

theorem fin15Anchored_clause19315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2608 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom0695 Fin15AnchoredAtom0697
    Fin15AnchoredAtom0816 Fin15AnchoredAtom1607 Fin15AnchoredAtom2608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14353
  ] at hbad
  tauto

theorem fin15Anchored_clause19316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2609 chi ∧
      ¬Fin15AnchoredAtom0696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0696 Fin15AnchoredAtom2609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22545
  ] at hbad
  tauto

theorem fin15Anchored_clause19317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2609 chi ∧
      ¬Fin15AnchoredAtom0817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0817 Fin15AnchoredAtom2609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22545
  ] at hbad
  tauto

theorem fin15Anchored_clause19318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28689
  ] at hbad
  tauto

theorem fin15Anchored_clause19319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom2611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28689
  ] at hbad
  tauto

theorem fin15Anchored_clause19320 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom2611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28689
  ] at hbad
  tauto

theorem fin15Anchored_clause19321 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28689
  ] at hbad
  tauto

theorem fin15Anchored_clause19322 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom2611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28689
  ] at hbad
  tauto

theorem fin15Anchored_clause19323 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom0698 Fin15AnchoredAtom0699
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1610 Fin15AnchoredAtom2611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28689
  ] at hbad
  tauto

theorem fin15Anchored_clause19324 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00481
  ] at hbad
  tauto

theorem fin15Anchored_clause19325 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom2612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00481
  ] at hbad
  tauto

theorem fin15Anchored_clause19326 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom2612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00481
  ] at hbad
  tauto

theorem fin15Anchored_clause19327 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2612 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom2612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00481
  ] at hbad
  tauto

end ErdosSzekeres

end
