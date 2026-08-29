module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment063

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 064. -/

theorem synchronizedFiveFanFin11Semantic_clause04609 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0555 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0186 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0186 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0555 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1555,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04610 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0555 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0201 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0201 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0555 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1555,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04611 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0555 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0264 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0555 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1555,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04612 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0555 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0348 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0555 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1555,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04613 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0555 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0555 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1009 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04614 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1009 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1555 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04615 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0555 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1009 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0555 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1009 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1555 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause04616 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1448 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0555 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0555 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04617 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1448 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0003 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0030 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0003 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0030 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1555 chi).mpr
  have hright0 : chi ⟨0, 1, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04618 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0555 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1448 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0555 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1448 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1555 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause04619 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0556 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0187 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0556 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0227,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04620 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0556 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0265 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0265 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0556 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0227,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04621 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0556 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0556 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0227,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04622 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0556 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0556 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1010 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04623 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1449 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0556 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0556 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1449 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04624 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0557 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0187 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0557 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0355,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04625 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0557 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0189 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0557 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0355,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04626 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0557 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0193 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0557 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0355,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04627 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0557 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0266 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0557 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0355,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04628 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0557 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0350 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0557 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0355,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04629 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0557 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0189 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0193 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0266 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0350 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0193 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0266 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0557 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0355,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04630 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0557 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0557 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1011 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04631 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0557 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0557 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04632 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1450 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1450 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0355 chi).mpr
  have hright0 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04633 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0187 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0558 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0611,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04634 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0190 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0558 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0611,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04635 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0194 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0558 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0611,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04636 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0558 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0611,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04637 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0351 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0558 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0611,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04638 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0558 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0187 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0190 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0194 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0351 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0194 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0267 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0558 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0611,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04639 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0558 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0558 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1012 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04640 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1012 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0611 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04641 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0558 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1012 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0558 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1012 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0611 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11Semantic_clause04642 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0558 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0558 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04643 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1451 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1451 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0611 chi).mpr
  have hright0 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04644 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0559 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0187 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0187 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0559 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1123,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04645 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0559 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0191 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0559 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1123,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04646 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0559 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0195 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0195 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0559 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1123,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04647 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0559 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0268 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0559 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1123,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04648 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0559 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0352 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0559 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1123,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04649 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0559 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0559 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1013 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04650 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0559 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0559 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04651 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1452 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0005 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0009 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0005 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0009 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1452 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1123 chi).mpr
  have hright0 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04652 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0560 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0188 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0560 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0419,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04653 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0560 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0189 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0560 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0419,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04654 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0560 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0196 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0196 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0560 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0419,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04655 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0560 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0269 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0269 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0560 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0419,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04656 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0560 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0353 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0560 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0419,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04657 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1014 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0560 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0560 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1014 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04658 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1453 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0560 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0560 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1453 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04659 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1453 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0040 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0076 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0150 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0040 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0076 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0150 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1453 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0419 chi).mpr
  have hright0 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 7, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 7, 8, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 7, 8, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 7, 8, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04660 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0561 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0188 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0188 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0561 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0675,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04661 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0561 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0190 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0561 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0675,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04662 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0561 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0197 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0197 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0561 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0675,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04663 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0561 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0354 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0561 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0675,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04664 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0561 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0561 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1015 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04665 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1454 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0561 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0561 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1454 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04666 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1454 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0006 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0006 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0041 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1454 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0675 chi).mpr
  have hright0 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 7, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04667 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0562 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0191 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0191 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0562 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1187,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04668 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0562 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0271 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0562 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1187,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04669 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0562 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0355 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0562 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1187,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04670 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0562 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0562 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1016 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04671 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1455 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0562 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0562 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1455 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04672 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0563 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0189 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0189 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0563 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0803,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04673 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0563 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0190 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0190 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0563 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0803,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04674 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0563 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0199 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0563 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0803,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04675 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0563 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0272 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0563 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0803,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04676 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0563 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0356 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0563 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0803,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04677 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0563 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0563 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1017 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04678 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1017 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0803 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04679 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1456 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0563 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0563 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1456 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04680 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1456 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0004 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0007 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0008 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0004 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0007 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0008 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1456 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0803 chi).mpr
  have hright0 : chi ⟨0, 1, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 1, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 1, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 1, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

end ErdosSzekeres

end
