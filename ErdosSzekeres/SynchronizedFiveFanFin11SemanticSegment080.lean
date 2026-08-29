module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment079

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 080. -/

theorem synchronizedFiveFanFin11Semantic_clause05761 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0285 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0701 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0286,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05762 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0289 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0701 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0286,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05763 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0701 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0286,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05764 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0316 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0701 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0286,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05765 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0701 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0286,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05766 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0701 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0285 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0316 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0295 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0316 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0701 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0286,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05767 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0701 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0701 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1152 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05768 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1591 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0701 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0701 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1591 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05769 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0702 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0285 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0702 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0542,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05770 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0702 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0290 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0702 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0542,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05771 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0702 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0296 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0296 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0702 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0542,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05772 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0702 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0317 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0317 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0702 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0542,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05773 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0702 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0702 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0542,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05774 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0702 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0702 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1153 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05775 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1153 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0542 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05776 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0702 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1153 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0702 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1153 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0542 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause05777 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1592 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0702 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0702 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1592 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05778 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0702 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1592 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0702 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1592 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0542 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h5)

theorem synchronizedFiveFanFin11Semantic_clause05779 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0285 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0703 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1054,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05780 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0291 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0703 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1054,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05781 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0297 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0297 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0703 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1054,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05782 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0318 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0318 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0703 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1054,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05783 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0373 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0703 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1054,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05784 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1154 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0703 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0703 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1154 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05785 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1154 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1054 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05786 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1593 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0703 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0703 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1593 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05787 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0703 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1593 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0703 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1593 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1054 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause05788 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0286 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0704 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05789 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0287 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0704 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05790 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0704 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05791 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0319 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0704 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05792 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0704 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05793 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0704 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0286 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0319 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0298 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0319 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0704 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0110,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05794 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0704 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0704 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1155 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05795 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1155 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0110 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05796 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1594 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0704 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0704 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1594 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05797 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0286 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0705 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05798 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0288 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0705 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05799 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0299 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0299 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0705 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05800 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0320 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0320 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0705 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05801 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0375 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0705 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0174,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05802 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1156 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0705 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0705 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1156 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05803 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1595 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0705 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0705 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1595 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05804 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0706 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0286 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0706 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05805 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0706 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0289 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0706 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05806 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0706 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0300 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0706 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05807 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0706 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0321 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0321 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0706 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05808 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0706 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0376 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0706 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0302,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05809 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1157 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0706 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0706 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1157 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05810 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1596 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0706 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0706 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1596 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05811 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0707 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0286 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0707 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05812 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0707 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0290 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0707 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05813 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0707 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0301 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0707 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05814 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0707 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0322 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0322 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0707 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05815 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0707 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0707 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0558,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05816 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1158 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0707 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0707 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1158 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05817 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1597 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0707 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0707 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1597 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05818 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0286 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0708 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1070,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05819 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0291 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0708 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1070,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05820 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0302 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0708 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1070,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05821 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0323 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0323 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0708 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1070,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05822 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0708 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1070,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05823 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0708 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0708 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1159 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05824 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1598 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0708 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0708 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1598 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05825 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0287 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0709 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0206,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05826 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0288 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0709 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0206,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05827 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0303 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0709 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0206,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05828 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0324 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0324 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0709 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0206,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05829 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0379 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0709 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0206,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05830 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0709 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0709 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1160 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05831 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0121 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1160 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0206 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05832 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1599 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0709 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0709 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1599 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
