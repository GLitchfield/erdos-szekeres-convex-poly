module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment093

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 094. -/

theorem synchronizedFiveFanFin11Semantic_clause06768 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0369 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0604,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06769 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0604,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06770 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0381 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0604,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06771 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0395 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0604,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06772 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0604,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06773 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0395 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0604,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06774 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1274 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0829 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1274 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06775 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1274 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1274 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0604 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06776 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1274 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0604 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06777 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1274 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0604 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause06778 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1274 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0604 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11Semantic_clause06779 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1274 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0604 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause06780 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1274 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0604 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06781 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1718 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0829 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1718 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06782 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0829 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1718 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0829 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1718 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0604 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06783 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0830 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0369 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1116,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06784 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0830 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0373 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1116,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06785 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0830 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1116,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06786 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0830 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1116,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06787 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0830 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1116,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06788 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1275 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0830 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1275 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06789 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1275 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1275 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1116 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06790 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0830 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1275 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1275 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1116 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h4

theorem synchronizedFiveFanFin11Semantic_clause06791 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0830 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1275 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1275 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1116 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause06792 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1719 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0830 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1719 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06793 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0830 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1719 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0830 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1719 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1116 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06794 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0831 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0370 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0831 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0412,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06795 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0831 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0831 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0412,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06796 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0831 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0432 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0432 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0831 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0412,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06797 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1276 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0831 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0831 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1276 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06798 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1720 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0831 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0831 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1720 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06799 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0832 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0370 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0832 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0668,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06800 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0832 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0832 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0668,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06801 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0832 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0383 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0832 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0668,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06802 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0832 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0398 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0398 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0832 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0668,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06803 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0832 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0832 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0668,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06804 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1277 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0832 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0832 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1277 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06805 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1277 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0141 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1277 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0668 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06806 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1721 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0832 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0832 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1721 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06807 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0833 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0370 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0833 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1180,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06808 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0833 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0373 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0833 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1180,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06809 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0833 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0399 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0399 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0833 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1180,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06810 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0833 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0434 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0833 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1180,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06811 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1278 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0833 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0833 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1278 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06812 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1722 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0833 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0833 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1722 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06813 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0834 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0834 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0796,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06814 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0834 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0834 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0796,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06815 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0834 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0385 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0834 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0796,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06816 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0834 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0400 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0400 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0834 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0796,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06817 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0834 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0435 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0834 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0796,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06818 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1279 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0834 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0834 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1279 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06819 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1279 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1279 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0796 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06820 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1723 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0834 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0834 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1723 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06821 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0835 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0835 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1308,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06822 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0835 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0373 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0835 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1308,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06823 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0835 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0386 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0835 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1308,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06824 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0835 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0401 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0401 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0835 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1308,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06825 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0835 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0436 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0835 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1308,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06826 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1280 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0835 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0835 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1280 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06827 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1280 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1280 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1308 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06828 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1724 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0835 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0835 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1724 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06829 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0836 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0836 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1564,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06830 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0836 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0373 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0836 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1564,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06831 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0836 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0387 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0836 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1564,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06832 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0836 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0402 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0836 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1564,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06833 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0836 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0836 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1564,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06834 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0836 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0372 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0373 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0402 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0402 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0836 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1564,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06835 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1281 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0836 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0836 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1281 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06836 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1281 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1281 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1564 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06837 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1725 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0836 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0836 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1725 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06838 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1725 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1725 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1564 chi).mpr
  have hright0 : chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

end ErdosSzekeres

end
