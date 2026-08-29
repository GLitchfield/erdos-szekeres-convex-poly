module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment064

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 065. -/

theorem synchronizedFiveFanFin11Semantic_clause04681 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0564 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0189 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0564 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1315,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04682 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0564 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0191 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0564 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1315,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04683 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0564 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0200 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0564 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1315,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04684 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0564 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0273 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0564 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1315,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04685 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0564 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0357 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0564 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1315,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04686 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1018 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0564 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0564 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1018 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04687 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1457 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0564 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0564 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1457 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04688 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0565 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0190 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0565 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1571,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04689 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0565 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0191 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0565 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1571,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04690 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0565 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0201 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0565 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1571,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04691 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0565 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0565 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1571,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04692 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0565 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0358 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0565 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1571,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04693 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0565 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0565 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1019 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04694 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1458 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0565 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0565 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1458 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04695 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0566 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0192 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0566 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0451,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04696 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0566 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0193 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0566 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0451,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04697 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0566 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0359 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0359 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0566 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0451,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04698 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0566 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0566 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1020 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04699 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1459 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0566 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0566 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1459 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04700 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0567 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0192 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0192 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0567 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0707,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04701 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0567 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0194 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0567 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0707,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04702 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0567 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0197 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0567 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0707,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04703 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0567 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0276 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0276 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0567 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0707,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04704 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0567 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0360 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0567 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0707,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04705 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1021 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0567 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0567 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1021 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04706 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1460 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0567 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0567 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1460 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04707 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1460 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0036 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1460 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0707 chi).mpr
  have hright0 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 7, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04708 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0568 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0195 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0568 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1219,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04709 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0568 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0277 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0277 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0568 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1219,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04710 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0568 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0361 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0568 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1219,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04711 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0568 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0568 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1022 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04712 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1461 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0568 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0568 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1461 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04713 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0569 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0193 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0835,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04714 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0569 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0194 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0835,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04715 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0569 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0835,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04716 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0569 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0278 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0835,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04717 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0569 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0362 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0835,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04718 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0569 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1023 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04719 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1023 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0835 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04720 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0569 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1023 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1023 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0835 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04721 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0569 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1023 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1023 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0835 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause04722 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1462 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0569 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04723 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0569 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0569 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1462 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0835 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11Semantic_clause04724 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0570 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0193 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0570 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1347,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04725 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0570 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0195 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0570 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1347,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04726 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0570 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0200 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0570 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1347,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04727 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0570 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0279 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0570 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1347,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04728 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0570 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0363 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0570 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1347,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04729 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0570 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0570 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1024 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04730 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1463 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0570 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0570 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1463 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04731 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0571 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0194 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0571 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1603,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04732 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0571 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0195 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0571 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1603,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04733 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0571 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0201 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0571 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1603,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04734 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0571 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0280 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0571 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1603,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04735 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0571 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0364 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0571 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1603,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04736 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0571 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0571 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1025 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04737 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0571 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0571 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1464 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04738 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1464 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1464 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1603 chi).mpr
  have hright0 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04739 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0572 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0198 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0198 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0572 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1411,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04740 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0572 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0365 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0365 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0572 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1411,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04741 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1465 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0572 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0572 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1465 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04742 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0573 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0198 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0198 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0573 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1667,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04743 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0573 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0201 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0573 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1667,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04744 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0573 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0283 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0573 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1667,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04745 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0573 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0366 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0573 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1667,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04746 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1466 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0573 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0573 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1466 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04747 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0574 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0574 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1795,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04748 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0574 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0200 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0200 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0574 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1795,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04749 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0574 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0201 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0574 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1795,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04750 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0574 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0284 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0574 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1795,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04751 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0574 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0367 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0574 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1795,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04752 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0574 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0574 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1026 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
