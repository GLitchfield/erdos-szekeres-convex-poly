module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment076

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 077. -/

theorem synchronizedFiveFanFin11Semantic_clause05545 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1561 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0668 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0668 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1561 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05546 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0669 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0251 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0669 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0689,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05547 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0669 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0253 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0669 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0689,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05548 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0669 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0669 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0689,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05549 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1121 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0669 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0669 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1121 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05550 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1562 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0669 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0669 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1562 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05551 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0251 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0251 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0670 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1201,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05552 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0254 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0670 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1201,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05553 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0670 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0463 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0670 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1201,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05554 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0670 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0670 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1122 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05555 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1563 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0670 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0670 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1563 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05556 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0252 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0671 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0817,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05557 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0253 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0671 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0817,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05558 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0262 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0671 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0817,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05559 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0272 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0671 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0817,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05560 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0671 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0671 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0817,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05561 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0671 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0671 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1123 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05562 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1564 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0671 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0671 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1564 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05563 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0252 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0252 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0672 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1329,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05564 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0254 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0672 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1329,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05565 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0263 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0672 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1329,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05566 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0273 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0672 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1329,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05567 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0672 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0672 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1329,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05568 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0672 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0672 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1124 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05569 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1565 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0672 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0672 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1565 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05570 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0673 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0253 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0253 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0673 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1585,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05571 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0673 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0254 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0254 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0673 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1585,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05572 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0673 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0264 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0264 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0673 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1585,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05573 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0673 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0673 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1585,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05574 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0673 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0673 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1585,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05575 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1125 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0673 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0673 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1125 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05576 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1566 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0673 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0673 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1566 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05577 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0674 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0255 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0674 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0465,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05578 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0674 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0256 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0674 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0465,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05579 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0674 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0259 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0259 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0674 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0465,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05580 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0674 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0275 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0275 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0674 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0465,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05581 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0674 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0467 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0467 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0674 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0465,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05582 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1126 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0674 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0674 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1126 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05583 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1567 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0674 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0674 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1567 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05584 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0255 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0675 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0721,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05585 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0257 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0675 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0721,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05586 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0260 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0260 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0675 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0721,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05587 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0276 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0276 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0675 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0721,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05588 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0675 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0675 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0721,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05589 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1127 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0675 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0675 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1127 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05590 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1568 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0675 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0675 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1568 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05591 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0255 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0255 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0676 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1233,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05592 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0258 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0676 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1233,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05593 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0261 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0261 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0676 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1233,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05594 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0676 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0469 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0676 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1233,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05595 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0676 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0676 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1128 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05596 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1569 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0676 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0676 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1569 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05597 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0256 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0849,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05598 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0257 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0849,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05599 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0262 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0262 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0849,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05600 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0278 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0849,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05601 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0849,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05602 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0677 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1129 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05603 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0028 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0029 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0028 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0029 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1129 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0849 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05604 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1129 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1129 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0849 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause05605 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0677 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1129 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1129 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0849 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause05606 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1570 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0677 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1570 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05607 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0677 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0026 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1570 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0026 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0677 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1570 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0849 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05608 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0678 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0256 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0256 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0678 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05609 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0678 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0258 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0678 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05610 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0678 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0263 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0263 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0678 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05611 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0678 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0279 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0678 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05612 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0678 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0678 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1361,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05613 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0678 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0678 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1130 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05614 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1571 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0678 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0678 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1571 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05615 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0257 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0257 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1617,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05616 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0258 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0258 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0679 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1617,
  ] at hbad
  tauto

end ErdosSzekeres

end
