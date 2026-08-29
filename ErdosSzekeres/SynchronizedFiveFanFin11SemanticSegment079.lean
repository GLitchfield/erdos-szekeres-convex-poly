module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment078

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 079. -/

theorem synchronizedFiveFanFin11Semantic_clause05689 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0280 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0689 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1633,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05690 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0689 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1633,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05691 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0689 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0689 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1141 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05692 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1141 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1141 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1633 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05693 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1581 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0689 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0689 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1581 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05694 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0690 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0272 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0690 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0929,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05695 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1582 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0690 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0690 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1582 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05696 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0691 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0269 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0269 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0691 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1441,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05697 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0691 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0271 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0691 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1441,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05698 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0691 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0273 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0691 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1441,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05699 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0691 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0691 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1142 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05700 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1583 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0691 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0691 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1583 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05701 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0270 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0270 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0692 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1697,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05702 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0271 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0692 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1697,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05703 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0692 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1697,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05704 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0283 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0692 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1697,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05705 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0692 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1697,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05706 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0692 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0692 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1143 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05707 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1584 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0692 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0692 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1584 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05708 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0272 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0693 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1825,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05709 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0273 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0693 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1825,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05710 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0693 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1825,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05711 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0284 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0693 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1825,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05712 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0693 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1825,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05713 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0693 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0693 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1144 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05714 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1585 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0693 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0693 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1585 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05715 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0277 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0277 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0694 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1473,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05716 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0279 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0694 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1473,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05717 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0694 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0694 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1145 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05718 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1586 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0694 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0694 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1586 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05719 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0276 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0276 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0695 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1729,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05720 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0277 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0277 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0695 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1729,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05721 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0280 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0695 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1729,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05722 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0283 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0283 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0695 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1729,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05723 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0695 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1729,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05724 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0695 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0695 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1146 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05725 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1587 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0695 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0695 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1587 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05726 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0278 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1857,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05727 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0279 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1857,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05728 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0280 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0280 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1857,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05729 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0284 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1857,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05730 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1857,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05731 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0696 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1147 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05732 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1147 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0044 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0044 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1147 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1857 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05733 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1147 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1857 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05734 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1147 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1857 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05735 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1147 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1857 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause05736 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1588 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0696 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0696 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1588 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05737 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0697 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0284 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0284 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0697 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1921,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05738 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0697 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0697 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1148 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05739 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0285 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0698 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0062,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05740 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0286 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0286 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0698 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0062,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05741 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0292 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0292 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0698 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0062,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05742 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0313 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0313 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0698 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0062,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05743 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0368 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0368 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0698 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0062,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05744 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0698 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0698 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1149 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05745 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0048 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0055 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0083 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0048 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0055 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0083 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1149 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0062 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05746 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1589 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0698 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0698 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1589 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05747 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0285 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0699 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0094,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05748 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0287 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0287 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0699 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0094,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05749 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0293 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0293 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0699 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0094,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05750 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0314 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0314 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0699 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0094,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05751 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0369 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0369 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0699 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0094,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05752 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1150 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0699 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0699 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1150 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05753 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1150 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0046 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0047 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0054 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0056 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0084 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0046 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0047 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0054 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0056 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0084 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1150 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0094 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05754 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0082 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1150 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0082 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0699 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1150 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0094 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05755 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1590 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0699 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0699 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1590 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05756 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0699 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1590 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0699 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1590 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0094 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause05757 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0285 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0285 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0700 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0158,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05758 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0294 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0294 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0700 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0158,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05759 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0315 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0315 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0700 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0158,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05760 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1151 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0700 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0700 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1151 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
