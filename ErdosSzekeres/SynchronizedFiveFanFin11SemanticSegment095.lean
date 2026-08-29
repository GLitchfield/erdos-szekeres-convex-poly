module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment094

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 095. -/

theorem synchronizedFiveFanFin11Semantic_clause06839 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0836 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1725 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0836 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1725 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1564 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06840 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0837 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0837 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0236,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06841 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0837 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0375 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0837 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0236,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06842 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0837 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0379 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0837 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0236,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06843 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0837 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0837 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0236,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06844 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0837 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0837 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0236,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06845 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0837 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0837 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1726 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06846 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1726 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1726 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0236 chi).mpr
  have hright0 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 7, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 7, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06847 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0838 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06848 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0838 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0376 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06849 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0838 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0380 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06850 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0838 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06851 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0838 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0364,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06852 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1282 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0838 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1282 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06853 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1282 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1282 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0364 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06854 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0838 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1727 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06855 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1727 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1727 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0364 chi).mpr
  have hright0 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06856 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0838 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1727 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1727 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0364 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause06857 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0838 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1727 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1727 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0364 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06858 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0838 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1727 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0838 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1727 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0364 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause06859 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06860 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06861 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0381 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06862 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0405 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06863 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06864 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0377 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0381 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0405 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0381 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0620,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06865 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1283 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0839 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1283 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06866 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1283 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1283 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0620 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06867 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1283 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1283 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause06868 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1728 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0839 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1728 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06869 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1728 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1728 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0620 chi).mpr
  have hright0 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06870 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1728 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1728 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause06871 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1728 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1728 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause06872 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1728 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1728 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause06873 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1728 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1728 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause06874 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1728 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1728 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06875 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0839 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1728 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0839 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1728 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0620 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause06876 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0840 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0840 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1132,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06877 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0840 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0840 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1132,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06878 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0840 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0382 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0382 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0840 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1132,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06879 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0840 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0840 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1132,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06880 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0840 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0840 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1132,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06881 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1284 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0840 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0840 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1284 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06882 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1284 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1284 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1132 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06883 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1729 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0840 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0840 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1729 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06884 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1729 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1729 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1132 chi).mpr
  have hright0 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 6, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06885 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0840 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1729 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0840 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1729 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1132 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause06886 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0841 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0375 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0841 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0428,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06887 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0841 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0407 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0407 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0841 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0428,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06888 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0841 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0442 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0442 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0841 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0428,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06889 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1285 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0841 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0841 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1285 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06890 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1730 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0841 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0841 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1730 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06891 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0842 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0375 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0842 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06892 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0842 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0842 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06893 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0842 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0383 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0383 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0842 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06894 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0842 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0408 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0408 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0842 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06895 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0842 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0842 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0684,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06896 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1286 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0842 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0842 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1286 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06897 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1731 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0842 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0842 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1731 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06898 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0843 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0375 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0843 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1196,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06899 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0843 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0843 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1196,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06900 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0843 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0409 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0409 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0843 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1196,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06901 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0843 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0843 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1196,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06902 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1287 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0843 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0843 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1287 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06903 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1732 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0843 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0843 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1732 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06904 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0844 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0376 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0844 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06905 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0844 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0844 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06906 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0844 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0385 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0844 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06907 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0844 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0410 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0410 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0844 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06908 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0844 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0844 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0812,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06909 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1288 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0844 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0844 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1288 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
