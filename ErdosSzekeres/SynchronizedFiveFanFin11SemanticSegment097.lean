module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment096

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 097. -/

theorem synchronizedFiveFanFin11Semantic_clause06981 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0851 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1740 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0851 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1740 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1612 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h5)

theorem synchronizedFiveFanFin11Semantic_clause06982 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0852 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0385 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0852 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0908,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06983 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0852 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0419 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0419 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0852 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0908,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06984 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1296 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0852 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0852 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1296 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06985 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1741 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0852 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0852 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1741 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06986 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0853 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0420 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0420 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0853 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1420,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06987 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1742 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0853 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0853 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1742 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06988 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0854 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0384 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0384 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0854 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1676,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06989 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0854 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0387 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0854 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1676,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06990 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0854 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0854 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1676,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06991 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1297 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0854 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0854 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1297 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06992 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1743 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0854 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0854 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1743 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06993 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0855 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0385 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1804,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06994 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0855 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0386 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1804,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06995 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0855 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0387 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1804,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06996 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0855 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1804,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06997 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0855 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1804,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06998 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0855 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0385 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0386 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0387 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0422 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0385 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0386 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0387 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1804,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06999 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1298 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0855 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1298 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07000 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1298 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0086 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0087 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0088 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0086 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0087 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0088 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1298 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1804 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07001 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0855 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1298 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1804 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause07002 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0855 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1298 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1298 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1804 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause07003 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1744 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0855 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0855 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1744 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07004 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0856 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0388 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0856 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0244,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07005 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0856 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0389 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0389 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0856 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0244,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07006 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0856 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0393 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0393 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0856 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0244,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07007 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0856 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0403 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0403 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0856 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0244,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07008 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0856 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0457 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0457 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0856 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0244,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07009 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1299 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0856 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0856 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1299 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07010 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1745 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0856 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0856 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1745 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07011 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0857 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0388 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0372,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07012 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0857 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0390 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0372,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07013 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0857 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0394 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0394 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0372,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07014 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0857 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0404 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0404 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0372,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07015 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0857 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0458 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0458 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0372,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07016 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1300 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0857 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1300 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07017 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1300 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0092 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0097 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0092 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0097 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1300 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0372 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07018 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0857 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1300 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0372 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause07019 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0857 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1300 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0372 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause07020 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0857 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1300 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1300 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0372 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause07021 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1746 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0857 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1746 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07022 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0857 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1746 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0857 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1746 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0372 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause07023 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0858 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0388 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0628,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07024 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0858 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0391 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0391 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0628,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07025 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0858 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0395 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0395 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0628,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07026 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0858 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0405 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0405 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0628,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07027 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0858 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0628,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07028 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1301 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0858 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1301 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07029 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1301 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0093 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0098 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0093 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0098 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1301 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0628 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07030 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0858 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1301 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0628 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause07031 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0858 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1301 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0628 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause07032 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0858 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1301 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1301 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0628 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause07033 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1747 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0858 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0858 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1747 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07034 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0388 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0388 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1140,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07035 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0392 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0392 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1140,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07036 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0396 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0396 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1140,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07037 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0406 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0406 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1140,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07038 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1140,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07039 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1302 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0859 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1302 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07040 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1302 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0089 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0094 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0095 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0089 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0094 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0095 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1302 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1140 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07041 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1302 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1140 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause07042 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1302 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1140 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause07043 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1302 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1302 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1140 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause07044 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1748 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0859 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1748 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07045 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0090 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1748 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0090 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1748 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1140 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h1)

theorem synchronizedFiveFanFin11Semantic_clause07046 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0859 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0099 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1748 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0099 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0859 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1748 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1140 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h4)

theorem synchronizedFiveFanFin11Semantic_clause07047 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0860 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0390 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0390 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0860 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0436,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07048 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0860 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0407 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0407 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0860 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0436,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07049 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0860 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0461 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0461 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0860 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0436,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07050 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1303 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0860 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0860 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1303 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07051 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0860 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0860 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1749 at hbad
  exact hbad.2 hbad.1.1

end ErdosSzekeres

end
