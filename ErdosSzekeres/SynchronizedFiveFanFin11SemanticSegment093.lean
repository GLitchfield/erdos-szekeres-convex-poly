module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment092

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 093. -/

theorem synchronizedFiveFanFin11Semantic_clause06697 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1710 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0821 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0821 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1710 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06698 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0124,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06699 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0369 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0124,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06700 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0374 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0124,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06701 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0388 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0124,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06702 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0124,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06703 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0368 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0369 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0374 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0388 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0423 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0374 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0423 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0124,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06704 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1267 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0822 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1267 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06705 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1267 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1267 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0124 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06706 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1267 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0124 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06707 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1267 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0124 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11Semantic_clause06708 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1267 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1267 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0124 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06709 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1711 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0822 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1711 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06710 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0822 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1711 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0822 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1711 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0124 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h7)

theorem synchronizedFiveFanFin11Semantic_clause06711 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0823 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0823 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0188,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06712 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0823 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0370 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0823 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0188,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06713 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0823 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0375 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0375 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0823 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0188,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06714 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0823 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0389 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0823 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0188,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06715 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0823 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0424 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0424 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0823 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0188,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06716 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1268 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0823 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0823 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1268 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06717 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1712 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0823 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0823 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1712 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06718 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1712 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0096 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0117 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0096 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0117 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1712 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0188 chi).mpr
  have hright0 : chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 7, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 7, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06719 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0824 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0824 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0316,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06720 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0824 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0824 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0316,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06721 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0824 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0376 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0376 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0824 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0316,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06722 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0824 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0390 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0824 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0316,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06723 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0824 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0824 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0316,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06724 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1269 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0824 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0824 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1269 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06725 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1713 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0824 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0824 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1713 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06726 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0825 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0572,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06727 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0825 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0372 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0372 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0572,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06728 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0825 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0377 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0377 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0572,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06729 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0825 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0391 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0572,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06730 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0825 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0572,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06731 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1270 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0825 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1270 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06732 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1270 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1270 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0572 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06733 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0825 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1270 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1270 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0572 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06734 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0825 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1270 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1270 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0572 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause06735 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1714 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0825 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1714 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06736 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0825 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1714 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0825 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1714 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0572 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause06737 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0826 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1084,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06738 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0826 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0373 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0373 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1084,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06739 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0826 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0378 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0378 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1084,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06740 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0826 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0392 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1084,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06741 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0826 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1084,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06742 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1271 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0826 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1271 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06743 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1271 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0135 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1271 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1084 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06744 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0826 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1271 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1084 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06745 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0826 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1271 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1084 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h2

theorem synchronizedFiveFanFin11Semantic_clause06746 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0826 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1271 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1084 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06747 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1715 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0826 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1715 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06748 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1715 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1715 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1084 chi).mpr
  have hright0 : chi ⟨2, 3, 4, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 4, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨2, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 3, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06749 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0826 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1715 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0826 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1715 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1084 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause06750 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0827 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0369 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0827 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0220,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06751 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0827 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0370 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0370 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0827 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0220,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06752 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0827 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0379 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0379 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0827 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0220,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06753 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0827 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0393 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0827 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0220,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06754 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0827 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0428 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0827 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0220,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06755 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1272 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0827 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0827 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1272 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06756 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1272 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0085 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0091 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0085 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0091 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1272 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0220 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06757 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1716 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0827 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0827 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1716 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06758 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0828 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0369 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0828 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0348,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06759 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0828 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0371 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0371 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0828 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0348,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06760 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0828 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0380 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0380 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0828 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0348,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06761 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0828 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0394 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0828 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0348,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06762 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0828 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0828 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0348,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06763 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1273 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0828 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0828 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1273 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06764 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1273 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1273 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0348 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06765 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0828 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1273 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0828 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1273 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0348 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause06766 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1717 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0828 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0828 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1717 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06767 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0828 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1717 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0828 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1717 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0348 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

end ErdosSzekeres

end
