module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment066

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 067. -/

theorem synchronizedFiveFanFin11Semantic_clause04825 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0583 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0206 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0583 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0301,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04826 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0583 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0217 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0217 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0583 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0301,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04827 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0583 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0238 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0583 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0301,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04828 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0583 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0376 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0583 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0301,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04829 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1035 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0583 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0583 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1035 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04830 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0583 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1035 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0583 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1035 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0301 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause04831 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1476 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0583 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0583 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1476 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04832 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0583 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0583 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1476 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0301 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause04833 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0584 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0203 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0584 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04834 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0584 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0207 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0584 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04835 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0584 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0218 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0584 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04836 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0584 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0584 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04837 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0584 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0584 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04838 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0584 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0203 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0207 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0218 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0239 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0218 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0584 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0557,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04839 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1036 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0584 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0584 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1036 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04840 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1477 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0584 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0584 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1477 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04841 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0585 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0203 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0203 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0585 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1069,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04842 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0585 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0208 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0585 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1069,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04843 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0585 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0219 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0219 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0585 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1069,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04844 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0585 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0585 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1069,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04845 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0585 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0585 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1069,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04846 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0585 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0585 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1037 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04847 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1478 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0585 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0585 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1478 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04848 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0586 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0204 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0586 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0205,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04849 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0586 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0205 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0205 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0586 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0205,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04850 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0586 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0220 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0220 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0586 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0205,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04851 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0586 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0241 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0241 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0586 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0205,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04852 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0586 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0379 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0586 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0205,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04853 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0586 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0586 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1038 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04854 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1479 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0586 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0586 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1479 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04855 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0587 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0204 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0333,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04856 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0587 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0206 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0333,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04857 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0587 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0221 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0221 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0333,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04858 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0587 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0242 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0333,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04859 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0587 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0380 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0333,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04860 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0587 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1039 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04861 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1039 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0333 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04862 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0587 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1039 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1039 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0333 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04863 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0587 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1039 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1039 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0333 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause04864 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0587 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1039 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1039 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0333 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause04865 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1480 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0587 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1480 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04866 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0587 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0015 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0015 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0587 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1480 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0333 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause04867 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0588 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0204 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0589,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04868 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0588 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0207 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0589,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04869 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0588 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0222 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0222 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0589,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04870 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0588 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0243 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0589,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04871 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0588 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0381 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0589,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04872 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1040 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0588 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1040 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04873 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1040 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1040 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0589 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04874 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0588 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1040 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1040 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0589 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04875 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0588 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1040 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1040 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0589 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h5

theorem synchronizedFiveFanFin11Semantic_clause04876 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1481 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0588 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1481 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04877 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1481 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0016 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0016 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1481 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0589 chi).mpr
  have hright0 : chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04878 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0588 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0588 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1481 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0589 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause04879 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0589 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0204 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0204 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1101,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04880 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0589 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0208 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0208 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1101,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04881 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0589 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0223 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0223 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1101,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04882 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0589 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0244 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1101,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04883 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0589 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1101,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04884 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1041 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0589 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1041 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04885 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1041 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1041 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1101 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause04886 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0589 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1041 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1041 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1101 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause04887 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0589 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1041 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1041 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1101 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause04888 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1482 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0589 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1482 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04889 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1482 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0010 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0013 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0010 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0013 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1482 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1101 chi).mpr
  have hright0 : chi ⟨0, 2, 3, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 3, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause04890 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0589 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0017 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0017 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0589 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1482 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1101 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause04891 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0590 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0205 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0205 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0590 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0397,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04892 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0590 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0206 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0206 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0590 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0397,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04893 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0590 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0224 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0224 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0590 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0397,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause04894 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1042 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0590 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0590 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1042 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04895 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1483 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0590 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0590 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1483 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause04896 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0591 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0207 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0207 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0591 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0653,
  ] at hbad
  tauto

end ErdosSzekeres

end
