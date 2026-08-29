module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment095

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 096. -/

theorem synchronizedFiveFanFin11Semantic_clause06910 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0844 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0844 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1733 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06911 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1733 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1733 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0812 chi).mpr
  have hright0 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06912 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0845 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0376 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0845 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1324,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06913 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0845 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0845 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1324,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06914 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0845 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0386 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0845 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1324,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06915 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0845 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0411 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0845 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1324,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06916 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0845 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0845 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1324,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06917 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0845 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0376 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0378 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0411 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0411 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0845 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1324,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06918 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1289 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0845 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0845 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1289 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06919 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1734 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0845 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0845 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1734 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06920 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0846 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0846 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1580,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06921 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0846 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0846 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1580,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06922 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0846 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0387 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0846 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1580,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06923 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0846 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0412 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0412 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0846 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1580,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06924 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0846 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0846 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1580,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06925 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1290 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0846 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0846 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1290 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06926 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1290 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1290 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1580 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06927 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0846 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1290 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0846 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1290 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1580 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h4

theorem synchronizedFiveFanFin11Semantic_clause06928 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1735 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0846 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0846 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1735 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06929 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0846 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1735 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0846 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1735 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1580 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause06930 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0847 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0379 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0847 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0716,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06931 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0847 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0381 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0847 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0716,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06932 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0847 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0383 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0847 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0716,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06933 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0847 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0414 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0847 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0716,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06934 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0847 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0449 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0847 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0716,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06935 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1291 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0847 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0847 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1291 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06936 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1736 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0847 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0847 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1736 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06937 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0848 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0379 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0848 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1228,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06938 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0848 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0848 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1228,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06939 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0848 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0384 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0848 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1228,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06940 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0848 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0415 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0848 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1228,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06941 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0848 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0450 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0848 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1228,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06942 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1292 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0848 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0848 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1292 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06943 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1737 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0848 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0848 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1737 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06944 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0380 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0844,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06945 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0381 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0844,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06946 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0385 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0844,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06947 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0416 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0844,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06948 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0844,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06949 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0416 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0844,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06950 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1293 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0849 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1293 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06951 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1293 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1293 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0844 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06952 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1293 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0844 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06953 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1293 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0844 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06954 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1738 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0849 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1738 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06955 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1738 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1738 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0844 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause06956 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0849 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1738 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0849 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1738 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0844 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06957 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0850 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0380 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1356,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06958 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0850 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1356,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06959 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0850 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0386 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1356,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06960 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0850 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0417 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1356,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06961 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0850 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1356,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06962 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0850 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0380 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0382 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0417 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1356,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06963 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1294 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0850 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1294 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06964 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1294 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1294 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1356 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06965 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1739 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0850 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1739 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06966 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1739 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1739 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1356 chi).mpr
  have hright0 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06967 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0850 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1739 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1739 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1356 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause06968 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0850 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1739 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0850 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1739 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1356 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause06969 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0851 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0381 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1612,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06970 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0851 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1612,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06971 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0851 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0387 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1612,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06972 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0851 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0418 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1612,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06973 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0851 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1612,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06974 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1295 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0851 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1295 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06975 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1295 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1295 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1612 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06976 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0851 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1295 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1612 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06977 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0851 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1295 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1612 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause06978 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0851 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1295 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1295 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1612 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause06979 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1740 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0851 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1740 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06980 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1740 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1740 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1612 chi).mpr
  have hright0 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

end ErdosSzekeres

end
