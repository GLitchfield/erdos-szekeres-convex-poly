module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment103

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 104. -/

theorem synchronizedFiveFanFin11Semantic_clause07478 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1358 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0917 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0917 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1358 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07479 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1799 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0917 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0917 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1799 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07480 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0918 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0442 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0442 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0918 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1448,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07481 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0918 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0918 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1448,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07482 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0918 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0918 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1448,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07483 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0918 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0484 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0484 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0918 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1448,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07484 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1359 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0918 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0918 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1359 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07485 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1800 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0918 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0918 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1800 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07486 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0919 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0919 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1704,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07487 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0919 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0919 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1704,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07488 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0919 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0919 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1704,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07489 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0919 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0919 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1704,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07490 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0919 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0919 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1704,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07491 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1360 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0919 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0919 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1360 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07492 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1801 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0919 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0919 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1801 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07493 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0920 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0920 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1832,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07494 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0920 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0920 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1832,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07495 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0920 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0920 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1832,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07496 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0920 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0920 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1832,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07497 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0920 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0920 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1832,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07498 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1361 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0920 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0920 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07499 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1361 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0154 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1361 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1832 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07500 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0920 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0920 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1802 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07501 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0921 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0921 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0968,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07502 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0921 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0921 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1803 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07503 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0922 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0450 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0922 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1480,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07504 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1362 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0922 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0922 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1362 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07505 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0923 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0449 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0923 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1736,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07506 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0923 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0450 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0923 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1736,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07507 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0923 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0923 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1736,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07508 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0923 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0923 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1736,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07509 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1363 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0923 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0923 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1363 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07510 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1804 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0923 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0923 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1804 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07511 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0924 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0924 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1864,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07512 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0924 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0924 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1864,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07513 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0924 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0924 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1864,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07514 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0924 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0924 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1864,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07515 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0924 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0924 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1864,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07516 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1364 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0924 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0924 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07517 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1364 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1364 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1864 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07518 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0924 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0924 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07519 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1805 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1864 chi).mpr
  have hright0 : chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨8, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07520 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0925 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0925 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1928,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07521 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1365 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0925 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0925 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1365 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07522 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0926 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0926 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0496,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07523 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0926 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0926 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0496,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07524 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1366 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0926 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0926 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1366 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07525 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1806 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0926 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0926 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1806 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07526 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0927 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0927 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0752,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07527 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0927 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0927 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0752,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07528 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0927 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0927 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0752,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07529 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0927 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0927 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0752,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07530 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1367 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0927 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0927 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1367 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07531 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1807 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0927 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0927 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1807 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07532 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0928 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0928 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1264,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07533 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0928 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0928 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1264,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07534 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0928 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0463 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0928 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1264,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07535 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0928 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0469 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0928 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1264,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07536 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1368 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0928 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0928 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1368 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07537 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1808 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0928 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0928 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1808 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07538 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1808 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0146 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0152 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0146 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0152 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1808 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1264 chi).mpr
  have hright0 : chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 7, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 7, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 7, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07539 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0929 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0929 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0880,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07540 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0929 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0929 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0880,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07541 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0929 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0929 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0880,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07542 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0929 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0929 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0880,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07543 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0929 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0929 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0880,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07544 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1369 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0929 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0929 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1369 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07545 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1809 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0929 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0929 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1809 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07546 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0930 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0930 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1392,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07547 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0930 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0930 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1392,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07548 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0930 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0930 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1392,
  ] at hbad
  tauto

end ErdosSzekeres

end
