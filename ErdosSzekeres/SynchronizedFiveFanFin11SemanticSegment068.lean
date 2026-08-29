module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment067

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 068. -/

theorem synchronizedFiveFanFin11Semantic_clause04897 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0591 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0591 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1043 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04898 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1484 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0591 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0591 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1484 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04899 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0592 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0208 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0592 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1165,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04900 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0592 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0226 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0226 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0592 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1165,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04901 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0592 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0246 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0246 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0592 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1165,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04902 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0592 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0384 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0592 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1165,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04903 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1044 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0592 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0592 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1044 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04904 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1485 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0592 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0592 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1485 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04905 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0593 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0206 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0781,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04906 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0593 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0207 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0781,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04907 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0593 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0227 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0227 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0781,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04908 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0593 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0247 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0781,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04909 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0593 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0385 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0781,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04910 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0593 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1045 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04911 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1045 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0781 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04912 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0593 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1045 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1045 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0781 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04913 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0593 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1045 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1045 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0781 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause04914 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0593 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1045 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1045 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0781 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause04915 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1486 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0593 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0593 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1486 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04916 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0594 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0206 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0594 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1293,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04917 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0594 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0208 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0594 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1293,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04918 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0594 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0228 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0228 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0594 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1293,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04919 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0594 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0248 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0594 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1293,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04920 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0594 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0386 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0594 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1293,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04921 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1046 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0594 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0594 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1046 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04922 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1046 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1293 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04923 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0594 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1046 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0594 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1046 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1293 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause04924 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1487 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0594 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0594 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1487 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04925 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0595 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0207 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0595 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1549,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04926 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0595 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0208 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0595 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1549,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04927 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0595 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0229 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0229 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0595 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1549,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04928 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0595 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0249 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0595 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1549,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04929 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0595 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0387 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0595 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1549,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04930 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1047 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0595 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0595 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1047 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04931 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1047 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1549 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04932 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0595 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1047 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0595 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1047 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1549 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause04933 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1488 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0595 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0595 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1488 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04934 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1488 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1488 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1549 chi).mpr
  have hright0 : chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04935 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0595 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1488 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0595 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1488 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1549 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause04936 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0596 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0117,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04937 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0596 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0210 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0210 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0117,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04938 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0596 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0215 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0215 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0117,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04939 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0596 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0250 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0250 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0117,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04940 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0596 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0388 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0117,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04941 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1048 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0596 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1048 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04942 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1048 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0117 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04943 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0596 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1048 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1048 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0117 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause04944 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0596 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1048 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1048 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0117 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause04945 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0596 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1048 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1048 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0117 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause04946 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1489 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0596 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1489 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04947 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0596 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0596 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1489 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0117 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause04948 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0597 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0597 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0181,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04949 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0597 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0211 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0211 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0597 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0181,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04950 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0597 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0216 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0216 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0597 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0181,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04951 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0597 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0251 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0597 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0181,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04952 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0597 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0389 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0597 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0181,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04953 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0597 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0597 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1049 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04954 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1490 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0597 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0597 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1490 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04955 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1490 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0011 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0012 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0014 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0025 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0027 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0032 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0011 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0012 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0014 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0025 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0027 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0032 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1490 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0181 chi).mpr
  have hright0 : chi ⟨0, 2, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 7, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 7, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04956 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0598 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0598 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0309,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04957 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0598 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0212 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0212 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0598 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0309,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04958 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0598 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0217 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0598 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0309,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04959 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0598 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0252 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0598 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0309,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04960 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0598 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0390 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0598 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0309,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04961 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0598 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0598 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1050 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04962 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1491 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0598 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0598 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1491 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04963 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0598 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1491 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0598 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1491 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0309 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause04964 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0599 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0209 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0209 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0599 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0565,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04965 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0599 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0213 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0213 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0599 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0565,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04966 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0599 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0218 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0599 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0565,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04967 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0599 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0253 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0599 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0565,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04968 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0599 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0391 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0599 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0565,
  ] at hbad
  tauto

end ErdosSzekeres

end
