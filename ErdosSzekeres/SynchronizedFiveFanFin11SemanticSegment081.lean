module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment080

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 081. -/

theorem synchronizedFiveFanFin11Semantic_clause05833 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0710 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0287 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0710 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0334,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05834 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0710 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0289 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0710 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0334,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05835 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0710 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0304 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0710 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0334,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05836 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0710 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0325 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0710 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0334,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05837 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0710 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0380 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0710 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0334,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05838 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0710 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0287 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0289 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0304 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0325 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0325 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0710 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0334,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05839 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0710 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0710 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1161 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05840 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1161 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0334 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05841 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1600 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0710 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0710 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1600 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05842 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0711 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0287 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0590,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05843 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0711 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0290 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0590,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05844 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0711 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0305 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0590,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05845 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0711 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0326 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0326 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0590,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05846 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0711 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0381 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0590,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05847 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1162 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0711 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1162 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05848 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1162 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1162 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0590 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05849 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0711 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1162 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1162 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0590 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05850 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0711 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1162 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1162 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0590 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05851 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1601 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0711 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1601 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05852 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0711 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1601 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0711 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1601 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0590 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause05853 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0712 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0287 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0712 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1102,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05854 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0712 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0291 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0712 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1102,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05855 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0712 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0306 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0712 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1102,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05856 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0712 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0327 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0327 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0712 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1102,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05857 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0712 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0712 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1102,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05858 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1163 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0712 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0712 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1163 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05859 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1163 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1163 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1102 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05860 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0712 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1163 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0712 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1163 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1102 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05861 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1602 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0712 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0712 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1602 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05862 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0712 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1602 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0712 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1602 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1102 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05863 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0713 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0289 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0713 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0398,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05864 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0713 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0328 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0328 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0713 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0398,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05865 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1603 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0713 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0713 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1603 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05866 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0714 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0288 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0714 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0654,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05867 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0714 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0290 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0714 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0654,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05868 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0714 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0308 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0714 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0654,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05869 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0714 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0329 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0329 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0714 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0654,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05870 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0714 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0383 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0714 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0654,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05871 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1164 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0714 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0714 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1164 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05872 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1164 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0057 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0057 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1164 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0654 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05873 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1604 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0714 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0714 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1604 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05874 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0715 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0288 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0288 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0715 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1166,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05875 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0715 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0291 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0715 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1166,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05876 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0715 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0309 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0715 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1166,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05877 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0715 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0330 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0330 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0715 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1166,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05878 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0715 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0384 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0715 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1166,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05879 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0715 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0715 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1165 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05880 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1605 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0715 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0715 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1605 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05881 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0716 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0289 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0716 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0782,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05882 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0716 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0290 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0716 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0782,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05883 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0716 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0310 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0716 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0782,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05884 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0716 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0331 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0331 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0716 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0782,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05885 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0716 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0385 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0716 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0782,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05886 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1166 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0716 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0716 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1166 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05887 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1166 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0058 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0058 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1166 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0782 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05888 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1606 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0716 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0716 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1606 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05889 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0717 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0289 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0289 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0717 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1294,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05890 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0717 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0291 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0717 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1294,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05891 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0717 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0311 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0717 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1294,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05892 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0717 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0332 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0332 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0717 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1294,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05893 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0717 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0386 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0717 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1294,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05894 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1167 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0717 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0717 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1167 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05895 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1607 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0717 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0717 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1607 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05896 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0718 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0290 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0290 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0718 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1550,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05897 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0718 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0291 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0291 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0718 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1550,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05898 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0718 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0312 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0718 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1550,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05899 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0718 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0333 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0333 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0718 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1550,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05900 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0718 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0387 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0718 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1550,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05901 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1168 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0718 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0718 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1168 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05902 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1168 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1168 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1550 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05903 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1608 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0718 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0718 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1608 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05904 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1608 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0059 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0060 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0059 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0060 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1608 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1550 chi).mpr
  have hright0 : chi ⟨1, 2, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

end ErdosSzekeres

end
