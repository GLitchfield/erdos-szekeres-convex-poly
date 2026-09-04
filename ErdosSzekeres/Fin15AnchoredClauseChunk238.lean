module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 238. -/

theorem fin15Anchored_clause30464 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4645 chi ∧
      Fin15AnchoredAtom4646 chi ∧
      Fin15AnchoredAtom4652 chi ∧
      Fin15AnchoredAtom4658 chi ∧
      Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom4793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4645 Fin15AnchoredAtom4646 Fin15AnchoredAtom4652
    Fin15AnchoredAtom4658 Fin15AnchoredAtom4688 Fin15AnchoredAtom4793 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 7, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {5, 9, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30465 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4650 chi ∧
      Fin15AnchoredAtom4651 chi ∧
      Fin15AnchoredAtom4652 chi ∧
      Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom4797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4650 Fin15AnchoredAtom4651 Fin15AnchoredAtom4652
    Fin15AnchoredAtom4662 Fin15AnchoredAtom4692 Fin15AnchoredAtom4797 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 7, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 9, 13, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30466 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4656 chi ∧
      Fin15AnchoredAtom4657 chi ∧
      Fin15AnchoredAtom4658 chi ∧
      Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom4801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4656 Fin15AnchoredAtom4657 Fin15AnchoredAtom4658
    Fin15AnchoredAtom4662 Fin15AnchoredAtom4696 Fin15AnchoredAtom4801 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 7, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 10, 13, 14}, {5, 7, 10, 12, 14}, {5, 7, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30467 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom4665 chi ∧
      Fin15AnchoredAtom4670 chi ∧
      Fin15AnchoredAtom4676 chi ∧
      Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom4806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4664 Fin15AnchoredAtom4665 Fin15AnchoredAtom4670
    Fin15AnchoredAtom4676 Fin15AnchoredAtom4686 Fin15AnchoredAtom4806 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 8, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 8, 10, 12, 13}, {5, 8, 9, 12, 13}, {5, 8, 9, 10, 13}, {5, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30468 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom4666 chi ∧
      Fin15AnchoredAtom4671 chi ∧
      Fin15AnchoredAtom4677 chi ∧
      Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom4807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4664 Fin15AnchoredAtom4666 Fin15AnchoredAtom4671
    Fin15AnchoredAtom4677 Fin15AnchoredAtom4687 Fin15AnchoredAtom4807 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 8, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 8, 10, 12, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30469 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4665 chi ∧
      Fin15AnchoredAtom4666 chi ∧
      Fin15AnchoredAtom4672 chi ∧
      Fin15AnchoredAtom4678 chi ∧
      Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom4808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4665 Fin15AnchoredAtom4666 Fin15AnchoredAtom4672
    Fin15AnchoredAtom4678 Fin15AnchoredAtom4688 Fin15AnchoredAtom4808 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 8, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {5, 9, 10, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 9, 13, 14}, {5, 8, 9, 10, 14}, {5, 8, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30470 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4670 chi ∧
      Fin15AnchoredAtom4671 chi ∧
      Fin15AnchoredAtom4672 chi ∧
      Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom4812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4670 Fin15AnchoredAtom4671 Fin15AnchoredAtom4672
    Fin15AnchoredAtom4682 Fin15AnchoredAtom4692 Fin15AnchoredAtom4812 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 8, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 8, 12, 13, 14}, {5, 8, 9, 13, 14}, {5, 8, 9, 12, 14}, {5, 8, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30471 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4676 chi ∧
      Fin15AnchoredAtom4677 chi ∧
      Fin15AnchoredAtom4678 chi ∧
      Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom4816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4676 Fin15AnchoredAtom4677 Fin15AnchoredAtom4678
    Fin15AnchoredAtom4682 Fin15AnchoredAtom4696 Fin15AnchoredAtom4816 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 8, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 8, 12, 13, 14}, {5, 8, 10, 13, 14}, {5, 8, 10, 12, 14}, {5, 8, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30472 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom4821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4686 Fin15AnchoredAtom4687 Fin15AnchoredAtom4688
    Fin15AnchoredAtom4692 Fin15AnchoredAtom4696 Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 9, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 9, 10, 13, 14}, {5, 9, 10, 12, 14}, {5, 9, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30473 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4698 chi ∧
      Fin15AnchoredAtom4700 chi ∧
      Fin15AnchoredAtom4704 chi ∧
      Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom4734 chi ∧
      Fin15AnchoredAtom4769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4698 Fin15AnchoredAtom4700 Fin15AnchoredAtom4704
    Fin15AnchoredAtom4714 Fin15AnchoredAtom4734 Fin15AnchoredAtom4769 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 12}, {6, 8, 9, 10, 12}, {6, 7, 9, 10, 12}, {6, 7, 8, 10, 12}, {6, 7, 8, 9, 12}, {6, 7, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30474 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4698 chi ∧
      Fin15AnchoredAtom4701 chi ∧
      Fin15AnchoredAtom4705 chi ∧
      Fin15AnchoredAtom4715 chi ∧
      Fin15AnchoredAtom4735 chi ∧
      Fin15AnchoredAtom4770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4698 Fin15AnchoredAtom4701 Fin15AnchoredAtom4705
    Fin15AnchoredAtom4715 Fin15AnchoredAtom4735 Fin15AnchoredAtom4770 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 13}, {6, 8, 9, 10, 13}, {6, 7, 9, 10, 13}, {6, 7, 8, 10, 13}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30475 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4698 chi ∧
      Fin15AnchoredAtom4702 chi ∧
      Fin15AnchoredAtom4706 chi ∧
      Fin15AnchoredAtom4716 chi ∧
      Fin15AnchoredAtom4736 chi ∧
      Fin15AnchoredAtom4771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4698 Fin15AnchoredAtom4702 Fin15AnchoredAtom4706
    Fin15AnchoredAtom4716 Fin15AnchoredAtom4736 Fin15AnchoredAtom4771 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 14}, {6, 8, 9, 10, 14}, {6, 7, 9, 10, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30476 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4700 chi ∧
      Fin15AnchoredAtom4701 chi ∧
      Fin15AnchoredAtom4710 chi ∧
      Fin15AnchoredAtom4720 chi ∧
      Fin15AnchoredAtom4740 chi ∧
      Fin15AnchoredAtom4775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4700 Fin15AnchoredAtom4701 Fin15AnchoredAtom4710
    Fin15AnchoredAtom4720 Fin15AnchoredAtom4740 Fin15AnchoredAtom4775 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 13}, {6, 8, 9, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 8, 12, 13}, {6, 7, 8, 9, 13}, {6, 7, 8, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30477 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4700 chi ∧
      Fin15AnchoredAtom4702 chi ∧
      Fin15AnchoredAtom4711 chi ∧
      Fin15AnchoredAtom4721 chi ∧
      Fin15AnchoredAtom4741 chi ∧
      Fin15AnchoredAtom4776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4700 Fin15AnchoredAtom4702 Fin15AnchoredAtom4711
    Fin15AnchoredAtom4721 Fin15AnchoredAtom4741 Fin15AnchoredAtom4776 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 14}, {6, 8, 9, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30478 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4701 chi ∧
      Fin15AnchoredAtom4702 chi ∧
      Fin15AnchoredAtom4712 chi ∧
      Fin15AnchoredAtom4722 chi ∧
      Fin15AnchoredAtom4742 chi ∧
      Fin15AnchoredAtom4777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4701 Fin15AnchoredAtom4702 Fin15AnchoredAtom4712
    Fin15AnchoredAtom4722 Fin15AnchoredAtom4742 Fin15AnchoredAtom4777 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 13, 14}, {6, 8, 9, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 8, 13, 14}, {6, 7, 8, 9, 14}, {6, 7, 8, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30479 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4704 chi ∧
      Fin15AnchoredAtom4705 chi ∧
      Fin15AnchoredAtom4710 chi ∧
      Fin15AnchoredAtom4726 chi ∧
      Fin15AnchoredAtom4746 chi ∧
      Fin15AnchoredAtom4781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4704 Fin15AnchoredAtom4705 Fin15AnchoredAtom4710
    Fin15AnchoredAtom4726 Fin15AnchoredAtom4746 Fin15AnchoredAtom4781 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 13}, {6, 8, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 8, 12, 13}, {6, 7, 8, 10, 13}, {6, 7, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30480 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4704 chi ∧
      Fin15AnchoredAtom4706 chi ∧
      Fin15AnchoredAtom4711 chi ∧
      Fin15AnchoredAtom4727 chi ∧
      Fin15AnchoredAtom4747 chi ∧
      Fin15AnchoredAtom4782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4704 Fin15AnchoredAtom4706 Fin15AnchoredAtom4711
    Fin15AnchoredAtom4727 Fin15AnchoredAtom4747 Fin15AnchoredAtom4782 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 14}, {6, 8, 10, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30481 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4705 chi ∧
      Fin15AnchoredAtom4706 chi ∧
      Fin15AnchoredAtom4712 chi ∧
      Fin15AnchoredAtom4728 chi ∧
      Fin15AnchoredAtom4748 chi ∧
      Fin15AnchoredAtom4783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4705 Fin15AnchoredAtom4706 Fin15AnchoredAtom4712
    Fin15AnchoredAtom4728 Fin15AnchoredAtom4748 Fin15AnchoredAtom4783 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 13, 14}, {6, 8, 10, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 8, 13, 14}, {6, 7, 8, 10, 14}, {6, 7, 8, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30482 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4710 chi ∧
      Fin15AnchoredAtom4711 chi ∧
      Fin15AnchoredAtom4712 chi ∧
      Fin15AnchoredAtom4732 chi ∧
      Fin15AnchoredAtom4752 chi ∧
      Fin15AnchoredAtom4787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4710 Fin15AnchoredAtom4711 Fin15AnchoredAtom4712
    Fin15AnchoredAtom4732 Fin15AnchoredAtom4752 Fin15AnchoredAtom4787 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 12, 13, 14}, {6, 8, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 8, 13, 14}, {6, 7, 8, 12, 14}, {6, 7, 8, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30483 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4713 chi ∧
      Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom4717 chi ∧
      Fin15AnchoredAtom4723 chi ∧
      Fin15AnchoredAtom4753 chi ∧
      Fin15AnchoredAtom4788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4713 Fin15AnchoredAtom4714 Fin15AnchoredAtom4717
    Fin15AnchoredAtom4723 Fin15AnchoredAtom4753 Fin15AnchoredAtom4788 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 9, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 11, 12}, {6, 9, 10, 11, 12}, {6, 7, 10, 11, 12}, {6, 7, 9, 11, 12}, {6, 7, 9, 10, 12}, {6, 7, 9, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30484 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom4715 chi ∧
      Fin15AnchoredAtom4720 chi ∧
      Fin15AnchoredAtom4726 chi ∧
      Fin15AnchoredAtom4756 chi ∧
      Fin15AnchoredAtom4791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4714 Fin15AnchoredAtom4715 Fin15AnchoredAtom4720
    Fin15AnchoredAtom4726 Fin15AnchoredAtom4756 Fin15AnchoredAtom4791 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 7, 10, 12, 13}, {6, 7, 9, 12, 13}, {6, 7, 9, 10, 13}, {6, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30485 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4714 chi ∧
      Fin15AnchoredAtom4716 chi ∧
      Fin15AnchoredAtom4721 chi ∧
      Fin15AnchoredAtom4727 chi ∧
      Fin15AnchoredAtom4757 chi ∧
      Fin15AnchoredAtom4792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4714 Fin15AnchoredAtom4716 Fin15AnchoredAtom4721
    Fin15AnchoredAtom4727 Fin15AnchoredAtom4757 Fin15AnchoredAtom4792 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 7, 10, 12, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30486 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4715 chi ∧
      Fin15AnchoredAtom4716 chi ∧
      Fin15AnchoredAtom4722 chi ∧
      Fin15AnchoredAtom4728 chi ∧
      Fin15AnchoredAtom4758 chi ∧
      Fin15AnchoredAtom4793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4715 Fin15AnchoredAtom4716 Fin15AnchoredAtom4722
    Fin15AnchoredAtom4728 Fin15AnchoredAtom4758 Fin15AnchoredAtom4793 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 10, 14}, {6, 7, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30487 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4720 chi ∧
      Fin15AnchoredAtom4721 chi ∧
      Fin15AnchoredAtom4722 chi ∧
      Fin15AnchoredAtom4732 chi ∧
      Fin15AnchoredAtom4762 chi ∧
      Fin15AnchoredAtom4797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4720 Fin15AnchoredAtom4721 Fin15AnchoredAtom4722
    Fin15AnchoredAtom4732 Fin15AnchoredAtom4762 Fin15AnchoredAtom4797 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 9, 13, 14}, {6, 7, 9, 12, 14}, {6, 7, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30488 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4726 chi ∧
      Fin15AnchoredAtom4727 chi ∧
      Fin15AnchoredAtom4728 chi ∧
      Fin15AnchoredAtom4732 chi ∧
      Fin15AnchoredAtom4766 chi ∧
      Fin15AnchoredAtom4801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4726 Fin15AnchoredAtom4727 Fin15AnchoredAtom4728
    Fin15AnchoredAtom4732 Fin15AnchoredAtom4766 Fin15AnchoredAtom4801 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 7, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 7, 12, 13, 14}, {6, 7, 10, 13, 14}, {6, 7, 10, 12, 14}, {6, 7, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30489 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4734 chi ∧
      Fin15AnchoredAtom4735 chi ∧
      Fin15AnchoredAtom4740 chi ∧
      Fin15AnchoredAtom4746 chi ∧
      Fin15AnchoredAtom4756 chi ∧
      Fin15AnchoredAtom4806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4734 Fin15AnchoredAtom4735 Fin15AnchoredAtom4740
    Fin15AnchoredAtom4746 Fin15AnchoredAtom4756 Fin15AnchoredAtom4806 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 8, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {6, 9, 10, 12, 13}, {6, 8, 10, 12, 13}, {6, 8, 9, 12, 13}, {6, 8, 9, 10, 13}, {6, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30490 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4734 chi ∧
      Fin15AnchoredAtom4736 chi ∧
      Fin15AnchoredAtom4741 chi ∧
      Fin15AnchoredAtom4747 chi ∧
      Fin15AnchoredAtom4757 chi ∧
      Fin15AnchoredAtom4807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4734 Fin15AnchoredAtom4736 Fin15AnchoredAtom4741
    Fin15AnchoredAtom4747 Fin15AnchoredAtom4757 Fin15AnchoredAtom4807 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 8, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {6, 9, 10, 12, 14}, {6, 8, 10, 12, 14}, {6, 8, 9, 12, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30491 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4735 chi ∧
      Fin15AnchoredAtom4736 chi ∧
      Fin15AnchoredAtom4742 chi ∧
      Fin15AnchoredAtom4748 chi ∧
      Fin15AnchoredAtom4758 chi ∧
      Fin15AnchoredAtom4808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4735 Fin15AnchoredAtom4736 Fin15AnchoredAtom4742
    Fin15AnchoredAtom4748 Fin15AnchoredAtom4758 Fin15AnchoredAtom4808 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 8, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {6, 9, 10, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 9, 13, 14}, {6, 8, 9, 10, 14}, {6, 8, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30492 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4740 chi ∧
      Fin15AnchoredAtom4741 chi ∧
      Fin15AnchoredAtom4742 chi ∧
      Fin15AnchoredAtom4752 chi ∧
      Fin15AnchoredAtom4762 chi ∧
      Fin15AnchoredAtom4812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4740 Fin15AnchoredAtom4741 Fin15AnchoredAtom4742
    Fin15AnchoredAtom4752 Fin15AnchoredAtom4762 Fin15AnchoredAtom4812 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 8, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 8, 12, 13, 14}, {6, 8, 9, 13, 14}, {6, 8, 9, 12, 14}, {6, 8, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30493 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4746 chi ∧
      Fin15AnchoredAtom4747 chi ∧
      Fin15AnchoredAtom4748 chi ∧
      Fin15AnchoredAtom4752 chi ∧
      Fin15AnchoredAtom4766 chi ∧
      Fin15AnchoredAtom4816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4746 Fin15AnchoredAtom4747 Fin15AnchoredAtom4748
    Fin15AnchoredAtom4752 Fin15AnchoredAtom4766 Fin15AnchoredAtom4816 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 8, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 8, 12, 13, 14}, {6, 8, 10, 13, 14}, {6, 8, 10, 12, 14}, {6, 8, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30494 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4756 chi ∧
      Fin15AnchoredAtom4757 chi ∧
      Fin15AnchoredAtom4758 chi ∧
      Fin15AnchoredAtom4762 chi ∧
      Fin15AnchoredAtom4766 chi ∧
      Fin15AnchoredAtom4821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4756 Fin15AnchoredAtom4757 Fin15AnchoredAtom4758
    Fin15AnchoredAtom4762 Fin15AnchoredAtom4766 Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{6, 9, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({6, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {6, 10, 12, 13, 14}, {6, 9, 12, 13, 14}, {6, 9, 10, 13, 14}, {6, 9, 10, 12, 14}, {6, 9, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30495 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4769 chi ∧
      Fin15AnchoredAtom4770 chi ∧
      Fin15AnchoredAtom4775 chi ∧
      Fin15AnchoredAtom4781 chi ∧
      Fin15AnchoredAtom4791 chi ∧
      Fin15AnchoredAtom4806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4769 Fin15AnchoredAtom4770 Fin15AnchoredAtom4775
    Fin15AnchoredAtom4781 Fin15AnchoredAtom4791 Fin15AnchoredAtom4806 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{7, 8, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({7, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {7, 9, 10, 12, 13}, {7, 8, 10, 12, 13}, {7, 8, 9, 12, 13}, {7, 8, 9, 10, 13}, {7, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30496 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4769 chi ∧
      Fin15AnchoredAtom4771 chi ∧
      Fin15AnchoredAtom4776 chi ∧
      Fin15AnchoredAtom4782 chi ∧
      Fin15AnchoredAtom4792 chi ∧
      Fin15AnchoredAtom4807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4769 Fin15AnchoredAtom4771 Fin15AnchoredAtom4776
    Fin15AnchoredAtom4782 Fin15AnchoredAtom4792 Fin15AnchoredAtom4807 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{7, 8, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({7, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {7, 9, 10, 12, 14}, {7, 8, 10, 12, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30497 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4770 chi ∧
      Fin15AnchoredAtom4771 chi ∧
      Fin15AnchoredAtom4777 chi ∧
      Fin15AnchoredAtom4783 chi ∧
      Fin15AnchoredAtom4793 chi ∧
      Fin15AnchoredAtom4808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4770 Fin15AnchoredAtom4771 Fin15AnchoredAtom4777
    Fin15AnchoredAtom4783 Fin15AnchoredAtom4793 Fin15AnchoredAtom4808 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{7, 8, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({7, 8, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 13, 14}, {7, 9, 10, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 10, 14}, {7, 8, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30498 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4775 chi ∧
      Fin15AnchoredAtom4776 chi ∧
      Fin15AnchoredAtom4777 chi ∧
      Fin15AnchoredAtom4787 chi ∧
      Fin15AnchoredAtom4797 chi ∧
      Fin15AnchoredAtom4812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4775 Fin15AnchoredAtom4776 Fin15AnchoredAtom4777
    Fin15AnchoredAtom4787 Fin15AnchoredAtom4797 Fin15AnchoredAtom4812 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{7, 8, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({7, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({7, 8, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 8, 12, 13, 14}, {7, 8, 9, 13, 14}, {7, 8, 9, 12, 14}, {7, 8, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30499 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4781 chi ∧
      Fin15AnchoredAtom4782 chi ∧
      Fin15AnchoredAtom4783 chi ∧
      Fin15AnchoredAtom4787 chi ∧
      Fin15AnchoredAtom4801 chi ∧
      Fin15AnchoredAtom4816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4781 Fin15AnchoredAtom4782 Fin15AnchoredAtom4783
    Fin15AnchoredAtom4787 Fin15AnchoredAtom4801 Fin15AnchoredAtom4816 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{7, 8, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({7, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 8, 12, 13, 14}, {7, 8, 10, 13, 14}, {7, 8, 10, 12, 14}, {7, 8, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30500 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4789 chi ∧
      Fin15AnchoredAtom4790 chi ∧
      Fin15AnchoredAtom4793 chi ∧
      Fin15AnchoredAtom4796 chi ∧
      Fin15AnchoredAtom4800 chi ∧
      Fin15AnchoredAtom4820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4789 Fin15AnchoredAtom4790 Fin15AnchoredAtom4793
    Fin15AnchoredAtom4796 Fin15AnchoredAtom4800 Fin15AnchoredAtom4820 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{7, 9, 10, 11, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({7, 9, 10, 11, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({7, 9, 10, 11, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 11, 13, 14}, {7, 10, 11, 13, 14}, {7, 9, 11, 13, 14}, {7, 9, 10, 13, 14}, {7, 9, 10, 11, 14}, {7, 9, 10, 11, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30501 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4791 chi ∧
      Fin15AnchoredAtom4792 chi ∧
      Fin15AnchoredAtom4793 chi ∧
      Fin15AnchoredAtom4797 chi ∧
      Fin15AnchoredAtom4801 chi ∧
      Fin15AnchoredAtom4821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4791 Fin15AnchoredAtom4792 Fin15AnchoredAtom4793
    Fin15AnchoredAtom4797 Fin15AnchoredAtom4801 Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{7, 9, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({7, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {7, 10, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 9, 10, 13, 14}, {7, 9, 10, 12, 14}, {7, 9, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30502 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4794 chi ∧
      Fin15AnchoredAtom4795 chi ∧
      Fin15AnchoredAtom4796 chi ∧
      Fin15AnchoredAtom4797 chi ∧
      Fin15AnchoredAtom4802 chi ∧
      Fin15AnchoredAtom4822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4794 Fin15AnchoredAtom4795 Fin15AnchoredAtom4796
    Fin15AnchoredAtom4797 Fin15AnchoredAtom4802 Fin15AnchoredAtom4822 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{7, 9, 11, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({7, 9, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({7, 9, 11, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 11, 12, 13, 14}, {7, 11, 12, 13, 14}, {7, 9, 12, 13, 14}, {7, 9, 11, 13, 14}, {7, 9, 11, 12, 14}, {7, 9, 11, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30503 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4806 chi ∧
      Fin15AnchoredAtom4807 chi ∧
      Fin15AnchoredAtom4808 chi ∧
      Fin15AnchoredAtom4812 chi ∧
      Fin15AnchoredAtom4816 chi ∧
      Fin15AnchoredAtom4821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4806 Fin15AnchoredAtom4807 Fin15AnchoredAtom4808
    Fin15AnchoredAtom4812 Fin15AnchoredAtom4816 Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{8, 9, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({8, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {8, 10, 12, 13, 14}, {8, 9, 12, 13, 14}, {8, 9, 10, 13, 14}, {8, 9, 10, 12, 14}, {8, 9, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30504 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3207 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom4032 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 6, 7}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00255
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1823
    Fin15AnchoredAtom1824 Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834
    Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1851 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1888 Fin15AnchoredAtom1889 Fin15AnchoredAtom1897 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1906 Fin15AnchoredAtom1942 Fin15AnchoredAtom1943 Fin15AnchoredAtom1951
    Fin15AnchoredAtom1987 Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109
    Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2126 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2163 Fin15AnchoredAtom2171 Fin15AnchoredAtom2207 Fin15AnchoredAtom2327
    Fin15AnchoredAtom2328 Fin15AnchoredAtom2336 Fin15AnchoredAtom2372 Fin15AnchoredAtom2492
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2832
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2841 Fin15AnchoredAtom2877 Fin15AnchoredAtom2878
    Fin15AnchoredAtom2886 Fin15AnchoredAtom2922 Fin15AnchoredAtom3042 Fin15AnchoredAtom3043
    Fin15AnchoredAtom3051 Fin15AnchoredAtom3087 Fin15AnchoredAtom3207 Fin15AnchoredAtom3537
    Fin15AnchoredAtom3538 Fin15AnchoredAtom3546 Fin15AnchoredAtom3582 Fin15AnchoredAtom3702
    Fin15AnchoredAtom4032 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30505 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3209 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom4034 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 6, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00639
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1823
    Fin15AnchoredAtom1826 Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1853 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1888 Fin15AnchoredAtom1891 Fin15AnchoredAtom1897 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1908 Fin15AnchoredAtom1942 Fin15AnchoredAtom1945 Fin15AnchoredAtom1953
    Fin15AnchoredAtom1989 Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2128 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2173 Fin15AnchoredAtom2209 Fin15AnchoredAtom2327
    Fin15AnchoredAtom2330 Fin15AnchoredAtom2338 Fin15AnchoredAtom2374 Fin15AnchoredAtom2494
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2832
    Fin15AnchoredAtom2835 Fin15AnchoredAtom2843 Fin15AnchoredAtom2877 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2888 Fin15AnchoredAtom2924 Fin15AnchoredAtom3042 Fin15AnchoredAtom3045
    Fin15AnchoredAtom3053 Fin15AnchoredAtom3089 Fin15AnchoredAtom3209 Fin15AnchoredAtom3537
    Fin15AnchoredAtom3540 Fin15AnchoredAtom3548 Fin15AnchoredAtom3584 Fin15AnchoredAtom3704
    Fin15AnchoredAtom4034 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30506 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3210 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom4035 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 6, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01151
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1823
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1854 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1888 Fin15AnchoredAtom1892 Fin15AnchoredAtom1897 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1909 Fin15AnchoredAtom1942 Fin15AnchoredAtom1946 Fin15AnchoredAtom1954
    Fin15AnchoredAtom1990 Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2129 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2174 Fin15AnchoredAtom2210 Fin15AnchoredAtom2327
    Fin15AnchoredAtom2331 Fin15AnchoredAtom2339 Fin15AnchoredAtom2375 Fin15AnchoredAtom2495
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2827 Fin15AnchoredAtom2832
    Fin15AnchoredAtom2836 Fin15AnchoredAtom2844 Fin15AnchoredAtom2877 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2889 Fin15AnchoredAtom2925 Fin15AnchoredAtom3042 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3054 Fin15AnchoredAtom3090 Fin15AnchoredAtom3210 Fin15AnchoredAtom3537
    Fin15AnchoredAtom3541 Fin15AnchoredAtom3549 Fin15AnchoredAtom3585 Fin15AnchoredAtom3705
    Fin15AnchoredAtom4035 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30507 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3212 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom4037 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 6, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04223
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1823
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1842 Fin15AnchoredAtom1848 Fin15AnchoredAtom1856 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1888 Fin15AnchoredAtom1894 Fin15AnchoredAtom1897 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1911 Fin15AnchoredAtom1942 Fin15AnchoredAtom1948 Fin15AnchoredAtom1956
    Fin15AnchoredAtom1992 Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2117 Fin15AnchoredAtom2123 Fin15AnchoredAtom2131 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2176 Fin15AnchoredAtom2212 Fin15AnchoredAtom2327
    Fin15AnchoredAtom2333 Fin15AnchoredAtom2341 Fin15AnchoredAtom2377 Fin15AnchoredAtom2497
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2829 Fin15AnchoredAtom2832
    Fin15AnchoredAtom2838 Fin15AnchoredAtom2846 Fin15AnchoredAtom2877 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2891 Fin15AnchoredAtom2927 Fin15AnchoredAtom3042 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3056 Fin15AnchoredAtom3092 Fin15AnchoredAtom3212 Fin15AnchoredAtom3537
    Fin15AnchoredAtom3543 Fin15AnchoredAtom3551 Fin15AnchoredAtom3587 Fin15AnchoredAtom3707
    Fin15AnchoredAtom4037 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30508 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3213 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom4038 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 6, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08319
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1823
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1842 Fin15AnchoredAtom1849 Fin15AnchoredAtom1857 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1888 Fin15AnchoredAtom1895 Fin15AnchoredAtom1897 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1912 Fin15AnchoredAtom1942 Fin15AnchoredAtom1949 Fin15AnchoredAtom1957
    Fin15AnchoredAtom1993 Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2117 Fin15AnchoredAtom2124 Fin15AnchoredAtom2132 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2177 Fin15AnchoredAtom2213 Fin15AnchoredAtom2327
    Fin15AnchoredAtom2334 Fin15AnchoredAtom2342 Fin15AnchoredAtom2378 Fin15AnchoredAtom2498
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2830 Fin15AnchoredAtom2832
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2847 Fin15AnchoredAtom2877 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2892 Fin15AnchoredAtom2928 Fin15AnchoredAtom3042 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3057 Fin15AnchoredAtom3093 Fin15AnchoredAtom3213 Fin15AnchoredAtom3537
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3552 Fin15AnchoredAtom3588 Fin15AnchoredAtom3708
    Fin15AnchoredAtom4038 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30509 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1942 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2162 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2327 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom3042 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3214 chi ∧
      ¬Fin15AnchoredAtom3537 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom4039 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 6, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16511
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1823
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1832 Fin15AnchoredAtom1833 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1842 Fin15AnchoredAtom1850 Fin15AnchoredAtom1858 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1888 Fin15AnchoredAtom1896 Fin15AnchoredAtom1897 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1913 Fin15AnchoredAtom1942 Fin15AnchoredAtom1950 Fin15AnchoredAtom1958
    Fin15AnchoredAtom1994 Fin15AnchoredAtom2107 Fin15AnchoredAtom2108 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2117 Fin15AnchoredAtom2125 Fin15AnchoredAtom2133 Fin15AnchoredAtom2162
    Fin15AnchoredAtom2170 Fin15AnchoredAtom2178 Fin15AnchoredAtom2214 Fin15AnchoredAtom2327
    Fin15AnchoredAtom2335 Fin15AnchoredAtom2343 Fin15AnchoredAtom2379 Fin15AnchoredAtom2499
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2823 Fin15AnchoredAtom2831 Fin15AnchoredAtom2832
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2848 Fin15AnchoredAtom2877 Fin15AnchoredAtom2885
    Fin15AnchoredAtom2893 Fin15AnchoredAtom2929 Fin15AnchoredAtom3042 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3058 Fin15AnchoredAtom3094 Fin15AnchoredAtom3214 Fin15AnchoredAtom3537
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3553 Fin15AnchoredAtom3589 Fin15AnchoredAtom3709
    Fin15AnchoredAtom4039 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30510 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3216 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom4041 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00703
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1826 Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1860 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1898 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1943 Fin15AnchoredAtom1945 Fin15AnchoredAtom1960
    Fin15AnchoredAtom1996 Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2135 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2165 Fin15AnchoredAtom2180 Fin15AnchoredAtom2216 Fin15AnchoredAtom2328
    Fin15AnchoredAtom2330 Fin15AnchoredAtom2345 Fin15AnchoredAtom2381 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2833
    Fin15AnchoredAtom2835 Fin15AnchoredAtom2850 Fin15AnchoredAtom2878 Fin15AnchoredAtom2880
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2931 Fin15AnchoredAtom3043 Fin15AnchoredAtom3045
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3096 Fin15AnchoredAtom3216 Fin15AnchoredAtom3538
    Fin15AnchoredAtom3540 Fin15AnchoredAtom3555 Fin15AnchoredAtom3591 Fin15AnchoredAtom3711
    Fin15AnchoredAtom4041 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30511 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3217 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom4042 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01215
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1861 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1892 Fin15AnchoredAtom1898 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1943 Fin15AnchoredAtom1946 Fin15AnchoredAtom1961
    Fin15AnchoredAtom1997 Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2136 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2181 Fin15AnchoredAtom2217 Fin15AnchoredAtom2328
    Fin15AnchoredAtom2331 Fin15AnchoredAtom2346 Fin15AnchoredAtom2382 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2827 Fin15AnchoredAtom2833
    Fin15AnchoredAtom2836 Fin15AnchoredAtom2851 Fin15AnchoredAtom2878 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2932 Fin15AnchoredAtom3043 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3097 Fin15AnchoredAtom3217 Fin15AnchoredAtom3538
    Fin15AnchoredAtom3541 Fin15AnchoredAtom3556 Fin15AnchoredAtom3592 Fin15AnchoredAtom3712
    Fin15AnchoredAtom4042 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30512 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3219 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom4044 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04287
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1843 Fin15AnchoredAtom1848 Fin15AnchoredAtom1863 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1894 Fin15AnchoredAtom1898 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1943 Fin15AnchoredAtom1948 Fin15AnchoredAtom1963
    Fin15AnchoredAtom1999 Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2118 Fin15AnchoredAtom2123 Fin15AnchoredAtom2138 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2183 Fin15AnchoredAtom2219 Fin15AnchoredAtom2328
    Fin15AnchoredAtom2333 Fin15AnchoredAtom2348 Fin15AnchoredAtom2384 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2829 Fin15AnchoredAtom2833
    Fin15AnchoredAtom2838 Fin15AnchoredAtom2853 Fin15AnchoredAtom2878 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2934 Fin15AnchoredAtom3043 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3099 Fin15AnchoredAtom3219 Fin15AnchoredAtom3538
    Fin15AnchoredAtom3543 Fin15AnchoredAtom3558 Fin15AnchoredAtom3594 Fin15AnchoredAtom3714
    Fin15AnchoredAtom4044 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30513 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3220 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom4045 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 7, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08383
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1843 Fin15AnchoredAtom1849 Fin15AnchoredAtom1864 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1895 Fin15AnchoredAtom1898 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1943 Fin15AnchoredAtom1949 Fin15AnchoredAtom1964
    Fin15AnchoredAtom2000 Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2118 Fin15AnchoredAtom2124 Fin15AnchoredAtom2139 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2184 Fin15AnchoredAtom2220 Fin15AnchoredAtom2328
    Fin15AnchoredAtom2334 Fin15AnchoredAtom2349 Fin15AnchoredAtom2385 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2830 Fin15AnchoredAtom2833
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2854 Fin15AnchoredAtom2878 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2935 Fin15AnchoredAtom3043 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3100 Fin15AnchoredAtom3220 Fin15AnchoredAtom3538
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3559 Fin15AnchoredAtom3595 Fin15AnchoredAtom3715
    Fin15AnchoredAtom4045 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30514 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1943 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2163 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2328 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom3043 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3221 chi ∧
      ¬Fin15AnchoredAtom3538 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom4046 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 7, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16575
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1832 Fin15AnchoredAtom1834 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1843 Fin15AnchoredAtom1850 Fin15AnchoredAtom1865 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1896 Fin15AnchoredAtom1898 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1920 Fin15AnchoredAtom1943 Fin15AnchoredAtom1950 Fin15AnchoredAtom1965
    Fin15AnchoredAtom2001 Fin15AnchoredAtom2107 Fin15AnchoredAtom2109 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2118 Fin15AnchoredAtom2125 Fin15AnchoredAtom2140 Fin15AnchoredAtom2163
    Fin15AnchoredAtom2170 Fin15AnchoredAtom2185 Fin15AnchoredAtom2221 Fin15AnchoredAtom2328
    Fin15AnchoredAtom2335 Fin15AnchoredAtom2350 Fin15AnchoredAtom2386 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2824 Fin15AnchoredAtom2831 Fin15AnchoredAtom2833
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2855 Fin15AnchoredAtom2878 Fin15AnchoredAtom2885
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2936 Fin15AnchoredAtom3043 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3101 Fin15AnchoredAtom3221 Fin15AnchoredAtom3538
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3560 Fin15AnchoredAtom3596 Fin15AnchoredAtom3716
    Fin15AnchoredAtom4046 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30515 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3228 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom4053 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01599
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1872 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1892 Fin15AnchoredAtom1900 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1945 Fin15AnchoredAtom1946 Fin15AnchoredAtom1972
    Fin15AnchoredAtom2008 Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2147 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2166 Fin15AnchoredAtom2192 Fin15AnchoredAtom2228 Fin15AnchoredAtom2330
    Fin15AnchoredAtom2331 Fin15AnchoredAtom2357 Fin15AnchoredAtom2393 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2836 Fin15AnchoredAtom2862 Fin15AnchoredAtom2880 Fin15AnchoredAtom2881
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2943 Fin15AnchoredAtom3045 Fin15AnchoredAtom3046
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3108 Fin15AnchoredAtom3228 Fin15AnchoredAtom3540
    Fin15AnchoredAtom3541 Fin15AnchoredAtom3567 Fin15AnchoredAtom3603 Fin15AnchoredAtom3723
    Fin15AnchoredAtom4053 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30516 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3230 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom4055 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04671
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1845 Fin15AnchoredAtom1848 Fin15AnchoredAtom1874 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1894 Fin15AnchoredAtom1900 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1945 Fin15AnchoredAtom1948 Fin15AnchoredAtom1974
    Fin15AnchoredAtom2010 Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2120 Fin15AnchoredAtom2123 Fin15AnchoredAtom2149 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2194 Fin15AnchoredAtom2230 Fin15AnchoredAtom2330
    Fin15AnchoredAtom2333 Fin15AnchoredAtom2359 Fin15AnchoredAtom2395 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2829 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2838 Fin15AnchoredAtom2864 Fin15AnchoredAtom2880 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2945 Fin15AnchoredAtom3045 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3110 Fin15AnchoredAtom3230 Fin15AnchoredAtom3540
    Fin15AnchoredAtom3543 Fin15AnchoredAtom3569 Fin15AnchoredAtom3605 Fin15AnchoredAtom3725
    Fin15AnchoredAtom4055 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30517 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3231 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom4056 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08767
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1845 Fin15AnchoredAtom1849 Fin15AnchoredAtom1875 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1895 Fin15AnchoredAtom1900 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1945 Fin15AnchoredAtom1949 Fin15AnchoredAtom1975
    Fin15AnchoredAtom2011 Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2120 Fin15AnchoredAtom2124 Fin15AnchoredAtom2150 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2195 Fin15AnchoredAtom2231 Fin15AnchoredAtom2330
    Fin15AnchoredAtom2334 Fin15AnchoredAtom2360 Fin15AnchoredAtom2396 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2830 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2865 Fin15AnchoredAtom2880 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2946 Fin15AnchoredAtom3045 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3111 Fin15AnchoredAtom3231 Fin15AnchoredAtom3540
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3570 Fin15AnchoredAtom3606 Fin15AnchoredAtom3726
    Fin15AnchoredAtom4056 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30518 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1945 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2165 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2330 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom3045 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3232 chi ∧
      ¬Fin15AnchoredAtom3540 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom4057 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16959
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1832 Fin15AnchoredAtom1836 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1845 Fin15AnchoredAtom1850 Fin15AnchoredAtom1876 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1896 Fin15AnchoredAtom1900 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1931 Fin15AnchoredAtom1945 Fin15AnchoredAtom1950 Fin15AnchoredAtom1976
    Fin15AnchoredAtom2012 Fin15AnchoredAtom2107 Fin15AnchoredAtom2111 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2120 Fin15AnchoredAtom2125 Fin15AnchoredAtom2151 Fin15AnchoredAtom2165
    Fin15AnchoredAtom2170 Fin15AnchoredAtom2196 Fin15AnchoredAtom2232 Fin15AnchoredAtom2330
    Fin15AnchoredAtom2335 Fin15AnchoredAtom2361 Fin15AnchoredAtom2397 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2826 Fin15AnchoredAtom2831 Fin15AnchoredAtom2835
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2866 Fin15AnchoredAtom2880 Fin15AnchoredAtom2885
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2947 Fin15AnchoredAtom3045 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3112 Fin15AnchoredAtom3232 Fin15AnchoredAtom3540
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3571 Fin15AnchoredAtom3607 Fin15AnchoredAtom3727
    Fin15AnchoredAtom4057 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30519 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3234 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom4059 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05183
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1832 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1846 Fin15AnchoredAtom1848 Fin15AnchoredAtom1878 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1894 Fin15AnchoredAtom1901 Fin15AnchoredAtom1903
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1946 Fin15AnchoredAtom1948 Fin15AnchoredAtom1978
    Fin15AnchoredAtom2014 Fin15AnchoredAtom2107 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2121 Fin15AnchoredAtom2123 Fin15AnchoredAtom2153 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2168 Fin15AnchoredAtom2198 Fin15AnchoredAtom2234 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2333 Fin15AnchoredAtom2363 Fin15AnchoredAtom2399 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2838 Fin15AnchoredAtom2868 Fin15AnchoredAtom2881 Fin15AnchoredAtom2883
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2949 Fin15AnchoredAtom3046 Fin15AnchoredAtom3048
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3114 Fin15AnchoredAtom3234 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3543 Fin15AnchoredAtom3573 Fin15AnchoredAtom3609 Fin15AnchoredAtom3729
    Fin15AnchoredAtom4059 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30520 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3235 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom4060 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09279
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1832 Fin15AnchoredAtom1837 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1846 Fin15AnchoredAtom1849 Fin15AnchoredAtom1879 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1895 Fin15AnchoredAtom1901 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1946 Fin15AnchoredAtom1949 Fin15AnchoredAtom1979
    Fin15AnchoredAtom2015 Fin15AnchoredAtom2107 Fin15AnchoredAtom2112 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2121 Fin15AnchoredAtom2124 Fin15AnchoredAtom2154 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2199 Fin15AnchoredAtom2235 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2334 Fin15AnchoredAtom2364 Fin15AnchoredAtom2400 Fin15AnchoredAtom2520
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2827 Fin15AnchoredAtom2830 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2869 Fin15AnchoredAtom2881 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2950 Fin15AnchoredAtom3046 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3115 Fin15AnchoredAtom3235 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3574 Fin15AnchoredAtom3610 Fin15AnchoredAtom3730
    Fin15AnchoredAtom4060 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30521 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1946 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2166 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2331 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom3046 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3236 chi ∧
      ¬Fin15AnchoredAtom3541 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom4061 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17471
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1832 Fin15AnchoredAtom1837 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1846 Fin15AnchoredAtom1850 Fin15AnchoredAtom1880 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1896 Fin15AnchoredAtom1901 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1935 Fin15AnchoredAtom1946 Fin15AnchoredAtom1950 Fin15AnchoredAtom1980
    Fin15AnchoredAtom2016 Fin15AnchoredAtom2107 Fin15AnchoredAtom2112 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2121 Fin15AnchoredAtom2125 Fin15AnchoredAtom2155 Fin15AnchoredAtom2166
    Fin15AnchoredAtom2170 Fin15AnchoredAtom2200 Fin15AnchoredAtom2236 Fin15AnchoredAtom2331
    Fin15AnchoredAtom2335 Fin15AnchoredAtom2365 Fin15AnchoredAtom2401 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2827 Fin15AnchoredAtom2831 Fin15AnchoredAtom2836
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2870 Fin15AnchoredAtom2881 Fin15AnchoredAtom2885
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2951 Fin15AnchoredAtom3046 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3116 Fin15AnchoredAtom3236 Fin15AnchoredAtom3541
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3575 Fin15AnchoredAtom3611 Fin15AnchoredAtom3731
    Fin15AnchoredAtom4061 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30522 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3240 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom4065 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12351
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1832 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1848 Fin15AnchoredAtom1849 Fin15AnchoredAtom1884 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1895 Fin15AnchoredAtom1903 Fin15AnchoredAtom1904
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1948 Fin15AnchoredAtom1949 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2020 Fin15AnchoredAtom2107 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2123 Fin15AnchoredAtom2124 Fin15AnchoredAtom2159 Fin15AnchoredAtom2168
    Fin15AnchoredAtom2169 Fin15AnchoredAtom2204 Fin15AnchoredAtom2240 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2334 Fin15AnchoredAtom2369 Fin15AnchoredAtom2405 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2839 Fin15AnchoredAtom2874 Fin15AnchoredAtom2883 Fin15AnchoredAtom2884
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2955 Fin15AnchoredAtom3048 Fin15AnchoredAtom3049
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3120 Fin15AnchoredAtom3240 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3544 Fin15AnchoredAtom3579 Fin15AnchoredAtom3615 Fin15AnchoredAtom3735
    Fin15AnchoredAtom4065 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30523 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1948 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2168 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2333 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom3048 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3241 chi ∧
      ¬Fin15AnchoredAtom3543 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom4066 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20543
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1832 Fin15AnchoredAtom1839 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1848 Fin15AnchoredAtom1850 Fin15AnchoredAtom1885 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1896 Fin15AnchoredAtom1903 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1940 Fin15AnchoredAtom1948 Fin15AnchoredAtom1950 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2021 Fin15AnchoredAtom2107 Fin15AnchoredAtom2114 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2123 Fin15AnchoredAtom2125 Fin15AnchoredAtom2160 Fin15AnchoredAtom2168
    Fin15AnchoredAtom2170 Fin15AnchoredAtom2205 Fin15AnchoredAtom2241 Fin15AnchoredAtom2333
    Fin15AnchoredAtom2335 Fin15AnchoredAtom2370 Fin15AnchoredAtom2406 Fin15AnchoredAtom2526
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2829 Fin15AnchoredAtom2831 Fin15AnchoredAtom2838
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2875 Fin15AnchoredAtom2883 Fin15AnchoredAtom2885
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2956 Fin15AnchoredAtom3048 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3121 Fin15AnchoredAtom3241 Fin15AnchoredAtom3543
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3580 Fin15AnchoredAtom3616 Fin15AnchoredAtom3736
    Fin15AnchoredAtom4066 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30524 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1832 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1949 chi ∧
      ¬Fin15AnchoredAtom1950 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2107 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2169 chi ∧
      ¬Fin15AnchoredAtom2170 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2334 chi ∧
      ¬Fin15AnchoredAtom2335 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom2822 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3049 chi ∧
      ¬Fin15AnchoredAtom3050 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3242 chi ∧
      ¬Fin15AnchoredAtom3544 chi ∧
      ¬Fin15AnchoredAtom3545 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom4067 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 5, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24639
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1822 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1832 Fin15AnchoredAtom1840 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1849 Fin15AnchoredAtom1850 Fin15AnchoredAtom1886 Fin15AnchoredAtom1887
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1896 Fin15AnchoredAtom1904 Fin15AnchoredAtom1905
    Fin15AnchoredAtom1941 Fin15AnchoredAtom1949 Fin15AnchoredAtom1950 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2022 Fin15AnchoredAtom2107 Fin15AnchoredAtom2115 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2124 Fin15AnchoredAtom2125 Fin15AnchoredAtom2161 Fin15AnchoredAtom2169
    Fin15AnchoredAtom2170 Fin15AnchoredAtom2206 Fin15AnchoredAtom2242 Fin15AnchoredAtom2334
    Fin15AnchoredAtom2335 Fin15AnchoredAtom2371 Fin15AnchoredAtom2407 Fin15AnchoredAtom2527
    Fin15AnchoredAtom2822 Fin15AnchoredAtom2830 Fin15AnchoredAtom2831 Fin15AnchoredAtom2839
    Fin15AnchoredAtom2840 Fin15AnchoredAtom2876 Fin15AnchoredAtom2884 Fin15AnchoredAtom2885
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2957 Fin15AnchoredAtom3049 Fin15AnchoredAtom3050
    Fin15AnchoredAtom3086 Fin15AnchoredAtom3122 Fin15AnchoredAtom3242 Fin15AnchoredAtom3544
    Fin15AnchoredAtom3545 Fin15AnchoredAtom3581 Fin15AnchoredAtom3617 Fin15AnchoredAtom3737
    Fin15AnchoredAtom4067 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30525 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3244 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom4069 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00735
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1826 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1860 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1891 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1951 Fin15AnchoredAtom1953 Fin15AnchoredAtom1960
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2135 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2173 Fin15AnchoredAtom2180 Fin15AnchoredAtom2244 Fin15AnchoredAtom2336
    Fin15AnchoredAtom2338 Fin15AnchoredAtom2345 Fin15AnchoredAtom2409 Fin15AnchoredAtom2529
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2850 Fin15AnchoredAtom2886 Fin15AnchoredAtom2888
    Fin15AnchoredAtom2895 Fin15AnchoredAtom2959 Fin15AnchoredAtom3051 Fin15AnchoredAtom3053
    Fin15AnchoredAtom3060 Fin15AnchoredAtom3124 Fin15AnchoredAtom3244 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3548 Fin15AnchoredAtom3555 Fin15AnchoredAtom3619 Fin15AnchoredAtom3739
    Fin15AnchoredAtom4069 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30526 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3245 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom4070 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01247
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1861 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1892 Fin15AnchoredAtom1906 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1951 Fin15AnchoredAtom1954 Fin15AnchoredAtom1961
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2136 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2181 Fin15AnchoredAtom2245 Fin15AnchoredAtom2336
    Fin15AnchoredAtom2339 Fin15AnchoredAtom2346 Fin15AnchoredAtom2410 Fin15AnchoredAtom2530
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2827 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2851 Fin15AnchoredAtom2886 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2896 Fin15AnchoredAtom2960 Fin15AnchoredAtom3051 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3061 Fin15AnchoredAtom3125 Fin15AnchoredAtom3245 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3549 Fin15AnchoredAtom3556 Fin15AnchoredAtom3620 Fin15AnchoredAtom3740
    Fin15AnchoredAtom4070 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30527 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3247 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom4072 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04319
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1863 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1894 Fin15AnchoredAtom1906 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1951 Fin15AnchoredAtom1956 Fin15AnchoredAtom1963
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2138 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2183 Fin15AnchoredAtom2247 Fin15AnchoredAtom2336
    Fin15AnchoredAtom2341 Fin15AnchoredAtom2348 Fin15AnchoredAtom2412 Fin15AnchoredAtom2532
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2829 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2853 Fin15AnchoredAtom2886 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2898 Fin15AnchoredAtom2962 Fin15AnchoredAtom3051 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3063 Fin15AnchoredAtom3127 Fin15AnchoredAtom3247 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3551 Fin15AnchoredAtom3558 Fin15AnchoredAtom3622 Fin15AnchoredAtom3742
    Fin15AnchoredAtom4072 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30528 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3248 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom4073 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 7, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08415
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1857 Fin15AnchoredAtom1864 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1895 Fin15AnchoredAtom1906 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1951 Fin15AnchoredAtom1957 Fin15AnchoredAtom1964
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2132 Fin15AnchoredAtom2139 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2184 Fin15AnchoredAtom2248 Fin15AnchoredAtom2336
    Fin15AnchoredAtom2342 Fin15AnchoredAtom2349 Fin15AnchoredAtom2413 Fin15AnchoredAtom2533
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2830 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2854 Fin15AnchoredAtom2886 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2899 Fin15AnchoredAtom2963 Fin15AnchoredAtom3051 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3064 Fin15AnchoredAtom3128 Fin15AnchoredAtom3248 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3559 Fin15AnchoredAtom3623 Fin15AnchoredAtom3743
    Fin15AnchoredAtom4073 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30529 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1951 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2171 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2336 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom3051 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3249 chi ∧
      ¬Fin15AnchoredAtom3546 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom4074 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 7, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16607
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1833 Fin15AnchoredAtom1834 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1858 Fin15AnchoredAtom1865 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1889 Fin15AnchoredAtom1896 Fin15AnchoredAtom1906 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1920 Fin15AnchoredAtom1951 Fin15AnchoredAtom1958 Fin15AnchoredAtom1965
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2108 Fin15AnchoredAtom2109 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2133 Fin15AnchoredAtom2140 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2178 Fin15AnchoredAtom2185 Fin15AnchoredAtom2249 Fin15AnchoredAtom2336
    Fin15AnchoredAtom2343 Fin15AnchoredAtom2350 Fin15AnchoredAtom2414 Fin15AnchoredAtom2534
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2824 Fin15AnchoredAtom2831 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2855 Fin15AnchoredAtom2886 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2900 Fin15AnchoredAtom2964 Fin15AnchoredAtom3051 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3065 Fin15AnchoredAtom3129 Fin15AnchoredAtom3249 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3560 Fin15AnchoredAtom3624 Fin15AnchoredAtom3744
    Fin15AnchoredAtom4074 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30530 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3256 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom4081 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01631
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1872 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1892 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1953 Fin15AnchoredAtom1954 Fin15AnchoredAtom1972
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2147 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2174 Fin15AnchoredAtom2192 Fin15AnchoredAtom2256 Fin15AnchoredAtom2338
    Fin15AnchoredAtom2339 Fin15AnchoredAtom2357 Fin15AnchoredAtom2421 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2862 Fin15AnchoredAtom2888 Fin15AnchoredAtom2889
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2971 Fin15AnchoredAtom3053 Fin15AnchoredAtom3054
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3136 Fin15AnchoredAtom3256 Fin15AnchoredAtom3548
    Fin15AnchoredAtom3549 Fin15AnchoredAtom3567 Fin15AnchoredAtom3631 Fin15AnchoredAtom3751
    Fin15AnchoredAtom4081 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30531 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3258 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom4083 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04703
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1874 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1894 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1953 Fin15AnchoredAtom1956 Fin15AnchoredAtom1974
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2149 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2194 Fin15AnchoredAtom2258 Fin15AnchoredAtom2338
    Fin15AnchoredAtom2341 Fin15AnchoredAtom2359 Fin15AnchoredAtom2423 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2829 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2864 Fin15AnchoredAtom2888 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2973 Fin15AnchoredAtom3053 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3138 Fin15AnchoredAtom3258 Fin15AnchoredAtom3548
    Fin15AnchoredAtom3551 Fin15AnchoredAtom3569 Fin15AnchoredAtom3633 Fin15AnchoredAtom3753
    Fin15AnchoredAtom4083 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30532 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3259 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom4084 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08799
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1857 Fin15AnchoredAtom1875 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1895 Fin15AnchoredAtom1908 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1953 Fin15AnchoredAtom1957 Fin15AnchoredAtom1975
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2132 Fin15AnchoredAtom2150 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2195 Fin15AnchoredAtom2259 Fin15AnchoredAtom2338
    Fin15AnchoredAtom2342 Fin15AnchoredAtom2360 Fin15AnchoredAtom2424 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2830 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2865 Fin15AnchoredAtom2888 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2974 Fin15AnchoredAtom3053 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3139 Fin15AnchoredAtom3259 Fin15AnchoredAtom3548
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3570 Fin15AnchoredAtom3634 Fin15AnchoredAtom3754
    Fin15AnchoredAtom4084 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30533 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1953 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2173 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2338 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom3053 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3260 chi ∧
      ¬Fin15AnchoredAtom3548 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom4085 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16991
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1833 Fin15AnchoredAtom1836 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1858 Fin15AnchoredAtom1876 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1896 Fin15AnchoredAtom1908 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1931 Fin15AnchoredAtom1953 Fin15AnchoredAtom1958 Fin15AnchoredAtom1976
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2108 Fin15AnchoredAtom2111 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2133 Fin15AnchoredAtom2151 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2178 Fin15AnchoredAtom2196 Fin15AnchoredAtom2260 Fin15AnchoredAtom2338
    Fin15AnchoredAtom2343 Fin15AnchoredAtom2361 Fin15AnchoredAtom2425 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2826 Fin15AnchoredAtom2831 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2866 Fin15AnchoredAtom2888 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2975 Fin15AnchoredAtom3053 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3140 Fin15AnchoredAtom3260 Fin15AnchoredAtom3548
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3571 Fin15AnchoredAtom3635 Fin15AnchoredAtom3755
    Fin15AnchoredAtom4085 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30534 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3262 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom4087 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05215
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1833 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1878 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1894 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1954 Fin15AnchoredAtom1956 Fin15AnchoredAtom1978
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2108 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2153 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2176 Fin15AnchoredAtom2198 Fin15AnchoredAtom2262 Fin15AnchoredAtom2339
    Fin15AnchoredAtom2341 Fin15AnchoredAtom2363 Fin15AnchoredAtom2427 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2868 Fin15AnchoredAtom2889 Fin15AnchoredAtom2891
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2977 Fin15AnchoredAtom3054 Fin15AnchoredAtom3056
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3142 Fin15AnchoredAtom3262 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3551 Fin15AnchoredAtom3573 Fin15AnchoredAtom3637 Fin15AnchoredAtom3757
    Fin15AnchoredAtom4087 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30535 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3263 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom4088 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09311
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1833 Fin15AnchoredAtom1837 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1857 Fin15AnchoredAtom1879 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1895 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1954 Fin15AnchoredAtom1957 Fin15AnchoredAtom1979
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2108 Fin15AnchoredAtom2112 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2129 Fin15AnchoredAtom2132 Fin15AnchoredAtom2154 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2199 Fin15AnchoredAtom2263 Fin15AnchoredAtom2339
    Fin15AnchoredAtom2342 Fin15AnchoredAtom2364 Fin15AnchoredAtom2428 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2827 Fin15AnchoredAtom2830 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2869 Fin15AnchoredAtom2889 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2978 Fin15AnchoredAtom3054 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3143 Fin15AnchoredAtom3263 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3574 Fin15AnchoredAtom3638 Fin15AnchoredAtom3758
    Fin15AnchoredAtom4088 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30536 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1954 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2174 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2339 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3054 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3264 chi ∧
      ¬Fin15AnchoredAtom3549 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom4089 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17503
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1833 Fin15AnchoredAtom1837 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1858 Fin15AnchoredAtom1880 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1896 Fin15AnchoredAtom1909 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1935 Fin15AnchoredAtom1954 Fin15AnchoredAtom1958 Fin15AnchoredAtom1980
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2108 Fin15AnchoredAtom2112 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2129 Fin15AnchoredAtom2133 Fin15AnchoredAtom2155 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2178 Fin15AnchoredAtom2200 Fin15AnchoredAtom2264 Fin15AnchoredAtom2339
    Fin15AnchoredAtom2343 Fin15AnchoredAtom2365 Fin15AnchoredAtom2429 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2827 Fin15AnchoredAtom2831 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2870 Fin15AnchoredAtom2889 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2915 Fin15AnchoredAtom2979 Fin15AnchoredAtom3054 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3144 Fin15AnchoredAtom3264 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3575 Fin15AnchoredAtom3639 Fin15AnchoredAtom3759
    Fin15AnchoredAtom4089 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30537 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3268 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom4093 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12383
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1833 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1856 Fin15AnchoredAtom1857 Fin15AnchoredAtom1884 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1895 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1956 Fin15AnchoredAtom1957 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2108 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2131 Fin15AnchoredAtom2132 Fin15AnchoredAtom2159 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2177 Fin15AnchoredAtom2204 Fin15AnchoredAtom2268 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2342 Fin15AnchoredAtom2369 Fin15AnchoredAtom2433 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2874 Fin15AnchoredAtom2891 Fin15AnchoredAtom2892
    Fin15AnchoredAtom2919 Fin15AnchoredAtom2983 Fin15AnchoredAtom3056 Fin15AnchoredAtom3057
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3148 Fin15AnchoredAtom3268 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3552 Fin15AnchoredAtom3579 Fin15AnchoredAtom3643 Fin15AnchoredAtom3763
    Fin15AnchoredAtom4093 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30538 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1956 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2176 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2341 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3056 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3269 chi ∧
      ¬Fin15AnchoredAtom3551 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom4094 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20575
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1833 Fin15AnchoredAtom1839 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1856 Fin15AnchoredAtom1858 Fin15AnchoredAtom1885 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1896 Fin15AnchoredAtom1911 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1940 Fin15AnchoredAtom1956 Fin15AnchoredAtom1958 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2108 Fin15AnchoredAtom2114 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2131 Fin15AnchoredAtom2133 Fin15AnchoredAtom2160 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2178 Fin15AnchoredAtom2205 Fin15AnchoredAtom2269 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2343 Fin15AnchoredAtom2370 Fin15AnchoredAtom2434 Fin15AnchoredAtom2554
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2829 Fin15AnchoredAtom2831 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2875 Fin15AnchoredAtom2891 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2920 Fin15AnchoredAtom2984 Fin15AnchoredAtom3056 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3149 Fin15AnchoredAtom3269 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3580 Fin15AnchoredAtom3644 Fin15AnchoredAtom3764
    Fin15AnchoredAtom4094 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30539 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1833 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1957 chi ∧
      ¬Fin15AnchoredAtom1958 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2108 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2177 chi ∧
      ¬Fin15AnchoredAtom2178 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2342 chi ∧
      ¬Fin15AnchoredAtom2343 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom2823 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3057 chi ∧
      ¬Fin15AnchoredAtom3058 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3270 chi ∧
      ¬Fin15AnchoredAtom3552 chi ∧
      ¬Fin15AnchoredAtom3553 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom4095 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 6, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24671
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1823 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1833 Fin15AnchoredAtom1840 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1857 Fin15AnchoredAtom1858 Fin15AnchoredAtom1886 Fin15AnchoredAtom1888
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1896 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1941 Fin15AnchoredAtom1957 Fin15AnchoredAtom1958 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2108 Fin15AnchoredAtom2115 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2132 Fin15AnchoredAtom2133 Fin15AnchoredAtom2161 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2178 Fin15AnchoredAtom2206 Fin15AnchoredAtom2270 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2343 Fin15AnchoredAtom2371 Fin15AnchoredAtom2435 Fin15AnchoredAtom2555
    Fin15AnchoredAtom2823 Fin15AnchoredAtom2830 Fin15AnchoredAtom2831 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2876 Fin15AnchoredAtom2892 Fin15AnchoredAtom2893
    Fin15AnchoredAtom2921 Fin15AnchoredAtom2985 Fin15AnchoredAtom3057 Fin15AnchoredAtom3058
    Fin15AnchoredAtom3086 Fin15AnchoredAtom3150 Fin15AnchoredAtom3270 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3553 Fin15AnchoredAtom3581 Fin15AnchoredAtom3645 Fin15AnchoredAtom3765
    Fin15AnchoredAtom4095 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30540 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3277 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom4102 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01695
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1872 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1892 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1960 Fin15AnchoredAtom1961 Fin15AnchoredAtom1972
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2147 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2181 Fin15AnchoredAtom2192 Fin15AnchoredAtom2277 Fin15AnchoredAtom2345
    Fin15AnchoredAtom2346 Fin15AnchoredAtom2357 Fin15AnchoredAtom2442 Fin15AnchoredAtom2562
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2862 Fin15AnchoredAtom2895 Fin15AnchoredAtom2896
    Fin15AnchoredAtom2907 Fin15AnchoredAtom2992 Fin15AnchoredAtom3060 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3072 Fin15AnchoredAtom3157 Fin15AnchoredAtom3277 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3556 Fin15AnchoredAtom3567 Fin15AnchoredAtom3652 Fin15AnchoredAtom3772
    Fin15AnchoredAtom4102 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30541 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3279 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom4104 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04767
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1874 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1894 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1960 Fin15AnchoredAtom1963 Fin15AnchoredAtom1974
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2149 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2194 Fin15AnchoredAtom2279 Fin15AnchoredAtom2345
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2359 Fin15AnchoredAtom2444 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2829 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2864 Fin15AnchoredAtom2895 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2909 Fin15AnchoredAtom2994 Fin15AnchoredAtom3060 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3074 Fin15AnchoredAtom3159 Fin15AnchoredAtom3279 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3569 Fin15AnchoredAtom3654 Fin15AnchoredAtom3774
    Fin15AnchoredAtom4104 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30542 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3280 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom4105 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08863
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1875 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1895 Fin15AnchoredAtom1915 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1960 Fin15AnchoredAtom1964 Fin15AnchoredAtom1975
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2150 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2195 Fin15AnchoredAtom2280 Fin15AnchoredAtom2345
    Fin15AnchoredAtom2349 Fin15AnchoredAtom2360 Fin15AnchoredAtom2445 Fin15AnchoredAtom2565
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2830 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2865 Fin15AnchoredAtom2895 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2910 Fin15AnchoredAtom2995 Fin15AnchoredAtom3060 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3075 Fin15AnchoredAtom3160 Fin15AnchoredAtom3280 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3570 Fin15AnchoredAtom3655 Fin15AnchoredAtom3775
    Fin15AnchoredAtom4105 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30543 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2180 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2345 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3060 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3281 chi ∧
      ¬Fin15AnchoredAtom3555 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom4106 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17055
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1834 Fin15AnchoredAtom1836 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1865 Fin15AnchoredAtom1876 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1891 Fin15AnchoredAtom1896 Fin15AnchoredAtom1915 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1931 Fin15AnchoredAtom1960 Fin15AnchoredAtom1965 Fin15AnchoredAtom1976
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2109 Fin15AnchoredAtom2111 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2140 Fin15AnchoredAtom2151 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2185 Fin15AnchoredAtom2196 Fin15AnchoredAtom2281 Fin15AnchoredAtom2345
    Fin15AnchoredAtom2350 Fin15AnchoredAtom2361 Fin15AnchoredAtom2446 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2826 Fin15AnchoredAtom2831 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2866 Fin15AnchoredAtom2895 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2911 Fin15AnchoredAtom2996 Fin15AnchoredAtom3060 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3076 Fin15AnchoredAtom3161 Fin15AnchoredAtom3281 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3571 Fin15AnchoredAtom3656 Fin15AnchoredAtom3776
    Fin15AnchoredAtom4106 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30544 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3283 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom4108 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05279
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1878 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1894 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1961 Fin15AnchoredAtom1963 Fin15AnchoredAtom1978
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2153 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2183 Fin15AnchoredAtom2198 Fin15AnchoredAtom2283 Fin15AnchoredAtom2346
    Fin15AnchoredAtom2348 Fin15AnchoredAtom2363 Fin15AnchoredAtom2448 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2868 Fin15AnchoredAtom2896 Fin15AnchoredAtom2898
    Fin15AnchoredAtom2913 Fin15AnchoredAtom2998 Fin15AnchoredAtom3061 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3163 Fin15AnchoredAtom3283 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3558 Fin15AnchoredAtom3573 Fin15AnchoredAtom3658 Fin15AnchoredAtom3778
    Fin15AnchoredAtom4108 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30545 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3284 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom4109 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09375
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1879 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1895 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1961 Fin15AnchoredAtom1964 Fin15AnchoredAtom1979
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2154 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2199 Fin15AnchoredAtom2284 Fin15AnchoredAtom2346
    Fin15AnchoredAtom2349 Fin15AnchoredAtom2364 Fin15AnchoredAtom2449 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2827 Fin15AnchoredAtom2830 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2869 Fin15AnchoredAtom2896 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2914 Fin15AnchoredAtom2999 Fin15AnchoredAtom3061 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3164 Fin15AnchoredAtom3284 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3574 Fin15AnchoredAtom3659 Fin15AnchoredAtom3779
    Fin15AnchoredAtom4109 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30546 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2181 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2346 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3061 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3285 chi ∧
      ¬Fin15AnchoredAtom3556 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom4110 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17567
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1834 Fin15AnchoredAtom1837 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1865 Fin15AnchoredAtom1880 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1896 Fin15AnchoredAtom1916 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1935 Fin15AnchoredAtom1961 Fin15AnchoredAtom1965 Fin15AnchoredAtom1980
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2109 Fin15AnchoredAtom2112 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2140 Fin15AnchoredAtom2155 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2185 Fin15AnchoredAtom2200 Fin15AnchoredAtom2285 Fin15AnchoredAtom2346
    Fin15AnchoredAtom2350 Fin15AnchoredAtom2365 Fin15AnchoredAtom2450 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2827 Fin15AnchoredAtom2831 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2870 Fin15AnchoredAtom2896 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2915 Fin15AnchoredAtom3000 Fin15AnchoredAtom3061 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3165 Fin15AnchoredAtom3285 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3575 Fin15AnchoredAtom3660 Fin15AnchoredAtom3780
    Fin15AnchoredAtom4110 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30547 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3289 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom4114 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12447
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1834 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1884 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1895 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1963 Fin15AnchoredAtom1964 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2109 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2159 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2184 Fin15AnchoredAtom2204 Fin15AnchoredAtom2289 Fin15AnchoredAtom2348
    Fin15AnchoredAtom2349 Fin15AnchoredAtom2369 Fin15AnchoredAtom2454 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2874 Fin15AnchoredAtom2898 Fin15AnchoredAtom2899
    Fin15AnchoredAtom2919 Fin15AnchoredAtom3004 Fin15AnchoredAtom3063 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3169 Fin15AnchoredAtom3289 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3559 Fin15AnchoredAtom3579 Fin15AnchoredAtom3664 Fin15AnchoredAtom3784
    Fin15AnchoredAtom4114 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30548 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2183 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2348 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3063 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3290 chi ∧
      ¬Fin15AnchoredAtom3558 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom4115 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20639
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1834 Fin15AnchoredAtom1839 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1865 Fin15AnchoredAtom1885 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1896 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1940 Fin15AnchoredAtom1963 Fin15AnchoredAtom1965 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2109 Fin15AnchoredAtom2114 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2140 Fin15AnchoredAtom2160 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2185 Fin15AnchoredAtom2205 Fin15AnchoredAtom2290 Fin15AnchoredAtom2348
    Fin15AnchoredAtom2350 Fin15AnchoredAtom2370 Fin15AnchoredAtom2455 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2829 Fin15AnchoredAtom2831 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2875 Fin15AnchoredAtom2898 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2920 Fin15AnchoredAtom3005 Fin15AnchoredAtom3063 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3170 Fin15AnchoredAtom3290 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3580 Fin15AnchoredAtom3665 Fin15AnchoredAtom3785
    Fin15AnchoredAtom4115 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30549 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1834 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2109 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2184 chi ∧
      ¬Fin15AnchoredAtom2185 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2349 chi ∧
      ¬Fin15AnchoredAtom2350 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom2824 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3064 chi ∧
      ¬Fin15AnchoredAtom3065 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3291 chi ∧
      ¬Fin15AnchoredAtom3559 chi ∧
      ¬Fin15AnchoredAtom3560 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom4116 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24735
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1824 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1834 Fin15AnchoredAtom1840 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1864 Fin15AnchoredAtom1865 Fin15AnchoredAtom1886 Fin15AnchoredAtom1889
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1896 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1941 Fin15AnchoredAtom1964 Fin15AnchoredAtom1965 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2109 Fin15AnchoredAtom2115 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2139 Fin15AnchoredAtom2140 Fin15AnchoredAtom2161 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2185 Fin15AnchoredAtom2206 Fin15AnchoredAtom2291 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2350 Fin15AnchoredAtom2371 Fin15AnchoredAtom2456 Fin15AnchoredAtom2576
    Fin15AnchoredAtom2824 Fin15AnchoredAtom2830 Fin15AnchoredAtom2831 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2876 Fin15AnchoredAtom2899 Fin15AnchoredAtom2900
    Fin15AnchoredAtom2921 Fin15AnchoredAtom3006 Fin15AnchoredAtom3064 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3086 Fin15AnchoredAtom3171 Fin15AnchoredAtom3291 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3560 Fin15AnchoredAtom3581 Fin15AnchoredAtom3666 Fin15AnchoredAtom3786
    Fin15AnchoredAtom4116 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30550 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2593 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3308 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom4133 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05663
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1894 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1972 Fin15AnchoredAtom1974 Fin15AnchoredAtom1978
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2194 Fin15AnchoredAtom2198 Fin15AnchoredAtom2308 Fin15AnchoredAtom2357
    Fin15AnchoredAtom2359 Fin15AnchoredAtom2363 Fin15AnchoredAtom2473 Fin15AnchoredAtom2593
    Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2829 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2907 Fin15AnchoredAtom2909
    Fin15AnchoredAtom2913 Fin15AnchoredAtom3023 Fin15AnchoredAtom3072 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3078 Fin15AnchoredAtom3188 Fin15AnchoredAtom3308 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3569 Fin15AnchoredAtom3573 Fin15AnchoredAtom3683 Fin15AnchoredAtom3803
    Fin15AnchoredAtom4133 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30551 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2594 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3309 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom4134 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09759
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1895 Fin15AnchoredAtom1927 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1972 Fin15AnchoredAtom1975 Fin15AnchoredAtom1979
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2199 Fin15AnchoredAtom2309 Fin15AnchoredAtom2357
    Fin15AnchoredAtom2360 Fin15AnchoredAtom2364 Fin15AnchoredAtom2474 Fin15AnchoredAtom2594
    Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2830 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2907 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2914 Fin15AnchoredAtom3024 Fin15AnchoredAtom3072 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3079 Fin15AnchoredAtom3189 Fin15AnchoredAtom3309 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3574 Fin15AnchoredAtom3684 Fin15AnchoredAtom3804
    Fin15AnchoredAtom4134 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30552 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2192 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2357 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2595 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3072 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3310 chi ∧
      ¬Fin15AnchoredAtom3567 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom4135 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17951
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1836 Fin15AnchoredAtom1837 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1892 Fin15AnchoredAtom1896 Fin15AnchoredAtom1927 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1935 Fin15AnchoredAtom1972 Fin15AnchoredAtom1976 Fin15AnchoredAtom1980
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2111 Fin15AnchoredAtom2112 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2196 Fin15AnchoredAtom2200 Fin15AnchoredAtom2310 Fin15AnchoredAtom2357
    Fin15AnchoredAtom2361 Fin15AnchoredAtom2365 Fin15AnchoredAtom2475 Fin15AnchoredAtom2595
    Fin15AnchoredAtom2826 Fin15AnchoredAtom2827 Fin15AnchoredAtom2831 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2907 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2915 Fin15AnchoredAtom3025 Fin15AnchoredAtom3072 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3080 Fin15AnchoredAtom3190 Fin15AnchoredAtom3310 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3575 Fin15AnchoredAtom3685 Fin15AnchoredAtom3805
    Fin15AnchoredAtom4135 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30553 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2599 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3314 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3809 chi ∧
      ¬Fin15AnchoredAtom4139 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12831
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1826 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1895 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1974 Fin15AnchoredAtom1975 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159 Fin15AnchoredAtom2194
    Fin15AnchoredAtom2195 Fin15AnchoredAtom2204 Fin15AnchoredAtom2314 Fin15AnchoredAtom2359
    Fin15AnchoredAtom2360 Fin15AnchoredAtom2369 Fin15AnchoredAtom2479 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2826 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2909 Fin15AnchoredAtom2910
    Fin15AnchoredAtom2919 Fin15AnchoredAtom3029 Fin15AnchoredAtom3074 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3194 Fin15AnchoredAtom3314 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3570 Fin15AnchoredAtom3579 Fin15AnchoredAtom3689 Fin15AnchoredAtom3809
    Fin15AnchoredAtom4139 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30554 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2194 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2359 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2600 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3074 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3315 chi ∧
      ¬Fin15AnchoredAtom3569 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3810 chi ∧
      ¬Fin15AnchoredAtom4140 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21023
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1826 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1836 Fin15AnchoredAtom1839 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1896 Fin15AnchoredAtom1929 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1940 Fin15AnchoredAtom1974 Fin15AnchoredAtom1976 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2111 Fin15AnchoredAtom2114 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160 Fin15AnchoredAtom2194
    Fin15AnchoredAtom2196 Fin15AnchoredAtom2205 Fin15AnchoredAtom2315 Fin15AnchoredAtom2359
    Fin15AnchoredAtom2361 Fin15AnchoredAtom2370 Fin15AnchoredAtom2480 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2826 Fin15AnchoredAtom2829 Fin15AnchoredAtom2831 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2909 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2920 Fin15AnchoredAtom3030 Fin15AnchoredAtom3074 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3195 Fin15AnchoredAtom3315 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3580 Fin15AnchoredAtom3690 Fin15AnchoredAtom3810
    Fin15AnchoredAtom4140 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30555 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1836 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2111 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2195 chi ∧
      ¬Fin15AnchoredAtom2196 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2360 chi ∧
      ¬Fin15AnchoredAtom2361 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2601 chi ∧
      ¬Fin15AnchoredAtom2826 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3075 chi ∧
      ¬Fin15AnchoredAtom3076 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3316 chi ∧
      ¬Fin15AnchoredAtom3570 chi ∧
      ¬Fin15AnchoredAtom3571 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3811 chi ∧
      ¬Fin15AnchoredAtom4141 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25119
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1826 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1836 Fin15AnchoredAtom1840 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom1891
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1896 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1941 Fin15AnchoredAtom1975 Fin15AnchoredAtom1976 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2111 Fin15AnchoredAtom2115 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2196 Fin15AnchoredAtom2206 Fin15AnchoredAtom2316 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2361 Fin15AnchoredAtom2371 Fin15AnchoredAtom2481 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2826 Fin15AnchoredAtom2830 Fin15AnchoredAtom2831 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2910 Fin15AnchoredAtom2911
    Fin15AnchoredAtom2921 Fin15AnchoredAtom3031 Fin15AnchoredAtom3075 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3086 Fin15AnchoredAtom3196 Fin15AnchoredAtom3316 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3571 Fin15AnchoredAtom3581 Fin15AnchoredAtom3691 Fin15AnchoredAtom3811
    Fin15AnchoredAtom4141 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30556 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2605 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3320 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3815 chi ∧
      ¬Fin15AnchoredAtom4145 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13343
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1895 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1978 Fin15AnchoredAtom1979 Fin15AnchoredAtom1984
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2198
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2204 Fin15AnchoredAtom2320 Fin15AnchoredAtom2363
    Fin15AnchoredAtom2364 Fin15AnchoredAtom2369 Fin15AnchoredAtom2485 Fin15AnchoredAtom2605
    Fin15AnchoredAtom2827 Fin15AnchoredAtom2829 Fin15AnchoredAtom2830 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2913 Fin15AnchoredAtom2914
    Fin15AnchoredAtom2919 Fin15AnchoredAtom3035 Fin15AnchoredAtom3078 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3084 Fin15AnchoredAtom3200 Fin15AnchoredAtom3320 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3574 Fin15AnchoredAtom3579 Fin15AnchoredAtom3695 Fin15AnchoredAtom3815
    Fin15AnchoredAtom4145 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30557 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom2101 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2198 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2321 chi ∧
      ¬Fin15AnchoredAtom2363 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom2606 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom3036 chi ∧
      ¬Fin15AnchoredAtom3078 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3201 chi ∧
      ¬Fin15AnchoredAtom3321 chi ∧
      ¬Fin15AnchoredAtom3573 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom3816 chi ∧
      ¬Fin15AnchoredAtom4146 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 10, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21535
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1837 Fin15AnchoredAtom1839 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1880 Fin15AnchoredAtom1885 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1894 Fin15AnchoredAtom1896 Fin15AnchoredAtom1933 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1940 Fin15AnchoredAtom1978 Fin15AnchoredAtom1980 Fin15AnchoredAtom1985
    Fin15AnchoredAtom2101 Fin15AnchoredAtom2112 Fin15AnchoredAtom2114 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160 Fin15AnchoredAtom2198
    Fin15AnchoredAtom2200 Fin15AnchoredAtom2205 Fin15AnchoredAtom2321 Fin15AnchoredAtom2363
    Fin15AnchoredAtom2365 Fin15AnchoredAtom2370 Fin15AnchoredAtom2486 Fin15AnchoredAtom2606
    Fin15AnchoredAtom2827 Fin15AnchoredAtom2829 Fin15AnchoredAtom2831 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2875 Fin15AnchoredAtom2913 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2920 Fin15AnchoredAtom3036 Fin15AnchoredAtom3078 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3085 Fin15AnchoredAtom3201 Fin15AnchoredAtom3321 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3580 Fin15AnchoredAtom3696 Fin15AnchoredAtom3816
    Fin15AnchoredAtom4146 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30558 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1837 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2102 chi ∧
      ¬Fin15AnchoredAtom2112 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2199 chi ∧
      ¬Fin15AnchoredAtom2200 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2322 chi ∧
      ¬Fin15AnchoredAtom2364 chi ∧
      ¬Fin15AnchoredAtom2365 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom2607 chi ∧
      ¬Fin15AnchoredAtom2827 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom3037 chi ∧
      ¬Fin15AnchoredAtom3079 chi ∧
      ¬Fin15AnchoredAtom3080 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3202 chi ∧
      ¬Fin15AnchoredAtom3322 chi ∧
      ¬Fin15AnchoredAtom3574 chi ∧
      ¬Fin15AnchoredAtom3575 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom3817 chi ∧
      ¬Fin15AnchoredAtom4147 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 10, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25631
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1827 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1837 Fin15AnchoredAtom1840 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1879 Fin15AnchoredAtom1880 Fin15AnchoredAtom1886 Fin15AnchoredAtom1892
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1896 Fin15AnchoredAtom1934 Fin15AnchoredAtom1935
    Fin15AnchoredAtom1941 Fin15AnchoredAtom1979 Fin15AnchoredAtom1980 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2102 Fin15AnchoredAtom2112 Fin15AnchoredAtom2115 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2200 Fin15AnchoredAtom2206 Fin15AnchoredAtom2322 Fin15AnchoredAtom2364
    Fin15AnchoredAtom2365 Fin15AnchoredAtom2371 Fin15AnchoredAtom2487 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2827 Fin15AnchoredAtom2830 Fin15AnchoredAtom2831 Fin15AnchoredAtom2869
    Fin15AnchoredAtom2870 Fin15AnchoredAtom2876 Fin15AnchoredAtom2914 Fin15AnchoredAtom2915
    Fin15AnchoredAtom2921 Fin15AnchoredAtom3037 Fin15AnchoredAtom3079 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3086 Fin15AnchoredAtom3202 Fin15AnchoredAtom3322 Fin15AnchoredAtom3574
    Fin15AnchoredAtom3575 Fin15AnchoredAtom3581 Fin15AnchoredAtom3697 Fin15AnchoredAtom3817
    Fin15AnchoredAtom4147 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30559 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1821 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1839 chi ∧
      ¬Fin15AnchoredAtom1840 chi ∧
      ¬Fin15AnchoredAtom1841 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom1986 chi ∧
      ¬Fin15AnchoredAtom2106 chi ∧
      ¬Fin15AnchoredAtom2114 chi ∧
      ¬Fin15AnchoredAtom2115 chi ∧
      ¬Fin15AnchoredAtom2116 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2204 chi ∧
      ¬Fin15AnchoredAtom2205 chi ∧
      ¬Fin15AnchoredAtom2206 chi ∧
      ¬Fin15AnchoredAtom2326 chi ∧
      ¬Fin15AnchoredAtom2369 chi ∧
      ¬Fin15AnchoredAtom2370 chi ∧
      ¬Fin15AnchoredAtom2371 chi ∧
      ¬Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom2611 chi ∧
      ¬Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2919 chi ∧
      ¬Fin15AnchoredAtom2920 chi ∧
      ¬Fin15AnchoredAtom2921 chi ∧
      ¬Fin15AnchoredAtom3041 chi ∧
      ¬Fin15AnchoredAtom3084 chi ∧
      ¬Fin15AnchoredAtom3085 chi ∧
      ¬Fin15AnchoredAtom3086 chi ∧
      ¬Fin15AnchoredAtom3206 chi ∧
      ¬Fin15AnchoredAtom3326 chi ∧
      ¬Fin15AnchoredAtom3579 chi ∧
      ¬Fin15AnchoredAtom3580 chi ∧
      ¬Fin15AnchoredAtom3581 chi ∧
      ¬Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom3821 chi ∧
      ¬Fin15AnchoredAtom4151 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 4, 12, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask28703
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1821 Fin15AnchoredAtom1829 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1839 Fin15AnchoredAtom1840 Fin15AnchoredAtom1841
    Fin15AnchoredAtom1884 Fin15AnchoredAtom1885 Fin15AnchoredAtom1886 Fin15AnchoredAtom1894
    Fin15AnchoredAtom1895 Fin15AnchoredAtom1896 Fin15AnchoredAtom1939 Fin15AnchoredAtom1940
    Fin15AnchoredAtom1941 Fin15AnchoredAtom1984 Fin15AnchoredAtom1985 Fin15AnchoredAtom1986
    Fin15AnchoredAtom2106 Fin15AnchoredAtom2114 Fin15AnchoredAtom2115 Fin15AnchoredAtom2116
    Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161 Fin15AnchoredAtom2204
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2206 Fin15AnchoredAtom2326 Fin15AnchoredAtom2369
    Fin15AnchoredAtom2370 Fin15AnchoredAtom2371 Fin15AnchoredAtom2491 Fin15AnchoredAtom2611
    Fin15AnchoredAtom2829 Fin15AnchoredAtom2830 Fin15AnchoredAtom2831 Fin15AnchoredAtom2874
    Fin15AnchoredAtom2875 Fin15AnchoredAtom2876 Fin15AnchoredAtom2919 Fin15AnchoredAtom2920
    Fin15AnchoredAtom2921 Fin15AnchoredAtom3041 Fin15AnchoredAtom3084 Fin15AnchoredAtom3085
    Fin15AnchoredAtom3086 Fin15AnchoredAtom3206 Fin15AnchoredAtom3326 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3580 Fin15AnchoredAtom3581 Fin15AnchoredAtom3701 Fin15AnchoredAtom3821
    Fin15AnchoredAtom4151 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30560 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2024 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2244 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2409 chi ∧
      ¬Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2959 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3124 chi ∧
      ¬Fin15AnchoredAtom3328 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom3823 chi ∧
      ¬Fin15AnchoredAtom4153 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 7, 9}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask00751
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1826 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1853 Fin15AnchoredAtom1860 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1898 Fin15AnchoredAtom1900 Fin15AnchoredAtom1906 Fin15AnchoredAtom1908
    Fin15AnchoredAtom1915 Fin15AnchoredAtom1987 Fin15AnchoredAtom1989 Fin15AnchoredAtom1996
    Fin15AnchoredAtom2024 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2135 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2209 Fin15AnchoredAtom2216 Fin15AnchoredAtom2244 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2374 Fin15AnchoredAtom2381 Fin15AnchoredAtom2409 Fin15AnchoredAtom2613
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2843 Fin15AnchoredAtom2850 Fin15AnchoredAtom2922 Fin15AnchoredAtom2924
    Fin15AnchoredAtom2931 Fin15AnchoredAtom2959 Fin15AnchoredAtom3087 Fin15AnchoredAtom3089
    Fin15AnchoredAtom3096 Fin15AnchoredAtom3124 Fin15AnchoredAtom3328 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3591 Fin15AnchoredAtom3619 Fin15AnchoredAtom3823
    Fin15AnchoredAtom4153 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30561 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2025 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2245 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2410 chi ∧
      ¬Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2960 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3125 chi ∧
      ¬Fin15AnchoredAtom3329 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom3824 chi ∧
      ¬Fin15AnchoredAtom4154 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 7, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01263
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1854 Fin15AnchoredAtom1861 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1898 Fin15AnchoredAtom1901 Fin15AnchoredAtom1906 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1916 Fin15AnchoredAtom1987 Fin15AnchoredAtom1990 Fin15AnchoredAtom1997
    Fin15AnchoredAtom2025 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2136 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2217 Fin15AnchoredAtom2245 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2375 Fin15AnchoredAtom2382 Fin15AnchoredAtom2410 Fin15AnchoredAtom2614
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2851 Fin15AnchoredAtom2922 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2932 Fin15AnchoredAtom2960 Fin15AnchoredAtom3087 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3097 Fin15AnchoredAtom3125 Fin15AnchoredAtom3329 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3592 Fin15AnchoredAtom3620 Fin15AnchoredAtom3824
    Fin15AnchoredAtom4154 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30562 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2027 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2247 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2412 chi ∧
      ¬Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2962 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3127 chi ∧
      ¬Fin15AnchoredAtom3331 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom3826 chi ∧
      ¬Fin15AnchoredAtom4156 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 7, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04335
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1856 Fin15AnchoredAtom1863 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1898 Fin15AnchoredAtom1903 Fin15AnchoredAtom1906 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1918 Fin15AnchoredAtom1987 Fin15AnchoredAtom1992 Fin15AnchoredAtom1999
    Fin15AnchoredAtom2027 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2138 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2219 Fin15AnchoredAtom2247 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2384 Fin15AnchoredAtom2412 Fin15AnchoredAtom2616
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2838 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2853 Fin15AnchoredAtom2922 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2934 Fin15AnchoredAtom2962 Fin15AnchoredAtom3087 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3099 Fin15AnchoredAtom3127 Fin15AnchoredAtom3331 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3594 Fin15AnchoredAtom3622 Fin15AnchoredAtom3826
    Fin15AnchoredAtom4156 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30563 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2028 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2248 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2413 chi ∧
      ¬Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2963 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3128 chi ∧
      ¬Fin15AnchoredAtom3332 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom3827 chi ∧
      ¬Fin15AnchoredAtom4157 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 7, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08431
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1857 Fin15AnchoredAtom1864 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1898 Fin15AnchoredAtom1904 Fin15AnchoredAtom1906 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1919 Fin15AnchoredAtom1987 Fin15AnchoredAtom1993 Fin15AnchoredAtom2000
    Fin15AnchoredAtom2028 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2132 Fin15AnchoredAtom2139 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2220 Fin15AnchoredAtom2248 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2385 Fin15AnchoredAtom2413 Fin15AnchoredAtom2617
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2839 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2854 Fin15AnchoredAtom2922 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2935 Fin15AnchoredAtom2963 Fin15AnchoredAtom3087 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3100 Fin15AnchoredAtom3128 Fin15AnchoredAtom3332 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3595 Fin15AnchoredAtom3623 Fin15AnchoredAtom3827
    Fin15AnchoredAtom4157 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30564 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1851 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1987 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2029 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2126 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2207 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2249 chi ∧
      ¬Fin15AnchoredAtom2372 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2414 chi ∧
      ¬Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2922 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2964 chi ∧
      ¬Fin15AnchoredAtom3087 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3129 chi ∧
      ¬Fin15AnchoredAtom3333 chi ∧
      ¬Fin15AnchoredAtom3582 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom3828 chi ∧
      ¬Fin15AnchoredAtom4158 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 7, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask16623
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1824
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1842 Fin15AnchoredAtom1843 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1851 Fin15AnchoredAtom1858 Fin15AnchoredAtom1865 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1898 Fin15AnchoredAtom1905 Fin15AnchoredAtom1906 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1920 Fin15AnchoredAtom1987 Fin15AnchoredAtom1994 Fin15AnchoredAtom2001
    Fin15AnchoredAtom2029 Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2126 Fin15AnchoredAtom2133 Fin15AnchoredAtom2140 Fin15AnchoredAtom2207
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2221 Fin15AnchoredAtom2249 Fin15AnchoredAtom2372
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2386 Fin15AnchoredAtom2414 Fin15AnchoredAtom2618
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2833 Fin15AnchoredAtom2840 Fin15AnchoredAtom2841
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2855 Fin15AnchoredAtom2922 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2936 Fin15AnchoredAtom2964 Fin15AnchoredAtom3087 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3101 Fin15AnchoredAtom3129 Fin15AnchoredAtom3333 Fin15AnchoredAtom3582
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3596 Fin15AnchoredAtom3624 Fin15AnchoredAtom3828
    Fin15AnchoredAtom4158 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30565 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2036 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2256 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2421 chi ∧
      ¬Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2971 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3136 chi ∧
      ¬Fin15AnchoredAtom3340 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom3835 chi ∧
      ¬Fin15AnchoredAtom4165 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01647
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1854 Fin15AnchoredAtom1872 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1908 Fin15AnchoredAtom1909
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1989 Fin15AnchoredAtom1990 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2036 Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2147 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2228 Fin15AnchoredAtom2256 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2375 Fin15AnchoredAtom2393 Fin15AnchoredAtom2421 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2844 Fin15AnchoredAtom2862 Fin15AnchoredAtom2924 Fin15AnchoredAtom2925
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2971 Fin15AnchoredAtom3089 Fin15AnchoredAtom3090
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3136 Fin15AnchoredAtom3340 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3603 Fin15AnchoredAtom3631 Fin15AnchoredAtom3835
    Fin15AnchoredAtom4165 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30566 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2038 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2258 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2423 chi ∧
      ¬Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2973 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom3342 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom3837 chi ∧
      ¬Fin15AnchoredAtom4167 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04719
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1856 Fin15AnchoredAtom1874 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1900 Fin15AnchoredAtom1903 Fin15AnchoredAtom1908 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1989 Fin15AnchoredAtom1992 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2038 Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2149 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2230 Fin15AnchoredAtom2258 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2395 Fin15AnchoredAtom2423 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2864 Fin15AnchoredAtom2924 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2973 Fin15AnchoredAtom3089 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3138 Fin15AnchoredAtom3342 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3605 Fin15AnchoredAtom3633 Fin15AnchoredAtom3837
    Fin15AnchoredAtom4167 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30567 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2039 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2259 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2424 chi ∧
      ¬Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2974 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom3343 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom3838 chi ∧
      ¬Fin15AnchoredAtom4168 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08815
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1857 Fin15AnchoredAtom1875 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1900 Fin15AnchoredAtom1904 Fin15AnchoredAtom1908 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1989 Fin15AnchoredAtom1993 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2039 Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2132 Fin15AnchoredAtom2150 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2231 Fin15AnchoredAtom2259 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2396 Fin15AnchoredAtom2424 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2839 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2865 Fin15AnchoredAtom2924 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2974 Fin15AnchoredAtom3089 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3139 Fin15AnchoredAtom3343 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3606 Fin15AnchoredAtom3634 Fin15AnchoredAtom3838
    Fin15AnchoredAtom4168 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30568 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1853 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1989 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2040 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2128 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2209 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2260 chi ∧
      ¬Fin15AnchoredAtom2374 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2425 chi ∧
      ¬Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2924 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2975 chi ∧
      ¬Fin15AnchoredAtom3089 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom3344 chi ∧
      ¬Fin15AnchoredAtom3584 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom3839 chi ∧
      ¬Fin15AnchoredAtom4169 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17007
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1842 Fin15AnchoredAtom1845 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1853 Fin15AnchoredAtom1858 Fin15AnchoredAtom1876 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1900 Fin15AnchoredAtom1905 Fin15AnchoredAtom1908 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1931 Fin15AnchoredAtom1989 Fin15AnchoredAtom1994 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2040 Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2128 Fin15AnchoredAtom2133 Fin15AnchoredAtom2151 Fin15AnchoredAtom2209
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2232 Fin15AnchoredAtom2260 Fin15AnchoredAtom2374
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2397 Fin15AnchoredAtom2425 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2835 Fin15AnchoredAtom2840 Fin15AnchoredAtom2843
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2866 Fin15AnchoredAtom2924 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2975 Fin15AnchoredAtom3089 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3140 Fin15AnchoredAtom3344 Fin15AnchoredAtom3584
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3607 Fin15AnchoredAtom3635 Fin15AnchoredAtom3839
    Fin15AnchoredAtom4169 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30569 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2042 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2262 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2427 chi ∧
      ¬Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2977 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom3346 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom3841 chi ∧
      ¬Fin15AnchoredAtom4171 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05231
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1856 Fin15AnchoredAtom1878 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1903 Fin15AnchoredAtom1909 Fin15AnchoredAtom1911
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1990 Fin15AnchoredAtom1992 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2042 Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2153 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2234 Fin15AnchoredAtom2262 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2399 Fin15AnchoredAtom2427 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2846 Fin15AnchoredAtom2868 Fin15AnchoredAtom2925 Fin15AnchoredAtom2927
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2977 Fin15AnchoredAtom3090 Fin15AnchoredAtom3092
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3142 Fin15AnchoredAtom3346 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3609 Fin15AnchoredAtom3637 Fin15AnchoredAtom3841
    Fin15AnchoredAtom4171 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30570 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2043 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2263 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2428 chi ∧
      ¬Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2978 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom3347 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom3842 chi ∧
      ¬Fin15AnchoredAtom4172 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09327
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1857 Fin15AnchoredAtom1879 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1904 Fin15AnchoredAtom1909 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1990 Fin15AnchoredAtom1993 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2043 Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2129 Fin15AnchoredAtom2132 Fin15AnchoredAtom2154 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2235 Fin15AnchoredAtom2263 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2400 Fin15AnchoredAtom2428 Fin15AnchoredAtom2632
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2869 Fin15AnchoredAtom2925 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2978 Fin15AnchoredAtom3090 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3143 Fin15AnchoredAtom3347 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3610 Fin15AnchoredAtom3638 Fin15AnchoredAtom3842
    Fin15AnchoredAtom4172 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30571 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1854 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1990 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2044 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2129 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2210 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2264 chi ∧
      ¬Fin15AnchoredAtom2375 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2429 chi ∧
      ¬Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2925 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom2979 chi ∧
      ¬Fin15AnchoredAtom3090 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom3348 chi ∧
      ¬Fin15AnchoredAtom3585 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom3843 chi ∧
      ¬Fin15AnchoredAtom4173 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17519
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1842 Fin15AnchoredAtom1846 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1854 Fin15AnchoredAtom1858 Fin15AnchoredAtom1880 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1905 Fin15AnchoredAtom1909 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1935 Fin15AnchoredAtom1990 Fin15AnchoredAtom1994 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2044 Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2129 Fin15AnchoredAtom2133 Fin15AnchoredAtom2155 Fin15AnchoredAtom2210
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2236 Fin15AnchoredAtom2264 Fin15AnchoredAtom2375
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2401 Fin15AnchoredAtom2429 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2836 Fin15AnchoredAtom2840 Fin15AnchoredAtom2844
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2870 Fin15AnchoredAtom2925 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2951 Fin15AnchoredAtom2979 Fin15AnchoredAtom3090 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3144 Fin15AnchoredAtom3348 Fin15AnchoredAtom3585
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3611 Fin15AnchoredAtom3639 Fin15AnchoredAtom3843
    Fin15AnchoredAtom4173 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30572 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2048 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2268 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2433 chi ∧
      ¬Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom2983 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom3352 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom3847 chi ∧
      ¬Fin15AnchoredAtom4177 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12399
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1842 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1856 Fin15AnchoredAtom1857 Fin15AnchoredAtom1884 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1904 Fin15AnchoredAtom1911 Fin15AnchoredAtom1912
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1992 Fin15AnchoredAtom1993 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2048 Fin15AnchoredAtom2117 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2131 Fin15AnchoredAtom2132 Fin15AnchoredAtom2159 Fin15AnchoredAtom2212
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2240 Fin15AnchoredAtom2268 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2405 Fin15AnchoredAtom2433 Fin15AnchoredAtom2637
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2847 Fin15AnchoredAtom2874 Fin15AnchoredAtom2927 Fin15AnchoredAtom2928
    Fin15AnchoredAtom2955 Fin15AnchoredAtom2983 Fin15AnchoredAtom3092 Fin15AnchoredAtom3093
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3148 Fin15AnchoredAtom3352 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3615 Fin15AnchoredAtom3643 Fin15AnchoredAtom3847
    Fin15AnchoredAtom4177 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30573 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1856 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1992 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2049 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2131 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2212 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2269 chi ∧
      ¬Fin15AnchoredAtom2377 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2434 chi ∧
      ¬Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2927 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom2984 chi ∧
      ¬Fin15AnchoredAtom3092 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom3353 chi ∧
      ¬Fin15AnchoredAtom3587 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom3848 chi ∧
      ¬Fin15AnchoredAtom4178 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20591
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1842 Fin15AnchoredAtom1848 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1856 Fin15AnchoredAtom1858 Fin15AnchoredAtom1885 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1905 Fin15AnchoredAtom1911 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1940 Fin15AnchoredAtom1992 Fin15AnchoredAtom1994 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2049 Fin15AnchoredAtom2117 Fin15AnchoredAtom2123 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2131 Fin15AnchoredAtom2133 Fin15AnchoredAtom2160 Fin15AnchoredAtom2212
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2241 Fin15AnchoredAtom2269 Fin15AnchoredAtom2377
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2406 Fin15AnchoredAtom2434 Fin15AnchoredAtom2638
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2838 Fin15AnchoredAtom2840 Fin15AnchoredAtom2846
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2875 Fin15AnchoredAtom2927 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2956 Fin15AnchoredAtom2984 Fin15AnchoredAtom3092 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3149 Fin15AnchoredAtom3353 Fin15AnchoredAtom3587
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3616 Fin15AnchoredAtom3644 Fin15AnchoredAtom3848
    Fin15AnchoredAtom4178 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30574 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1823 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1842 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1857 chi ∧
      ¬Fin15AnchoredAtom1858 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom1913 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom1993 chi ∧
      ¬Fin15AnchoredAtom1994 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2050 chi ∧
      ¬Fin15AnchoredAtom2117 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2132 chi ∧
      ¬Fin15AnchoredAtom2133 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2213 chi ∧
      ¬Fin15AnchoredAtom2214 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2270 chi ∧
      ¬Fin15AnchoredAtom2378 chi ∧
      ¬Fin15AnchoredAtom2379 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2435 chi ∧
      ¬Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2928 chi ∧
      ¬Fin15AnchoredAtom2929 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom2985 chi ∧
      ¬Fin15AnchoredAtom3093 chi ∧
      ¬Fin15AnchoredAtom3094 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom3354 chi ∧
      ¬Fin15AnchoredAtom3588 chi ∧
      ¬Fin15AnchoredAtom3589 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom3849 chi ∧
      ¬Fin15AnchoredAtom4179 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 6, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24687
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1823 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1842 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1857 Fin15AnchoredAtom1858 Fin15AnchoredAtom1886 Fin15AnchoredAtom1897
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1905 Fin15AnchoredAtom1912 Fin15AnchoredAtom1913
    Fin15AnchoredAtom1941 Fin15AnchoredAtom1993 Fin15AnchoredAtom1994 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2050 Fin15AnchoredAtom2117 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2132 Fin15AnchoredAtom2133 Fin15AnchoredAtom2161 Fin15AnchoredAtom2213
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2242 Fin15AnchoredAtom2270 Fin15AnchoredAtom2378
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2407 Fin15AnchoredAtom2435 Fin15AnchoredAtom2639
    Fin15AnchoredAtom2832 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840 Fin15AnchoredAtom2847
    Fin15AnchoredAtom2848 Fin15AnchoredAtom2876 Fin15AnchoredAtom2928 Fin15AnchoredAtom2929
    Fin15AnchoredAtom2957 Fin15AnchoredAtom2985 Fin15AnchoredAtom3093 Fin15AnchoredAtom3094
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3150 Fin15AnchoredAtom3354 Fin15AnchoredAtom3588
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3617 Fin15AnchoredAtom3645 Fin15AnchoredAtom3849
    Fin15AnchoredAtom4179 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30575 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2057 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2277 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2442 chi ∧
      ¬Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2992 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom3361 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom3856 chi ∧
      ¬Fin15AnchoredAtom4186 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 9, 10}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask01711
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1827 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1861 Fin15AnchoredAtom1872 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1900 Fin15AnchoredAtom1901 Fin15AnchoredAtom1915 Fin15AnchoredAtom1916
    Fin15AnchoredAtom1927 Fin15AnchoredAtom1996 Fin15AnchoredAtom1997 Fin15AnchoredAtom2008
    Fin15AnchoredAtom2057 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2147 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2228 Fin15AnchoredAtom2277 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2393 Fin15AnchoredAtom2442 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2851 Fin15AnchoredAtom2862 Fin15AnchoredAtom2931 Fin15AnchoredAtom2932
    Fin15AnchoredAtom2943 Fin15AnchoredAtom2992 Fin15AnchoredAtom3096 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3108 Fin15AnchoredAtom3157 Fin15AnchoredAtom3361 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3603 Fin15AnchoredAtom3652 Fin15AnchoredAtom3856
    Fin15AnchoredAtom4186 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30576 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2059 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2279 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2444 chi ∧
      ¬Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2994 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom3363 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom3858 chi ∧
      ¬Fin15AnchoredAtom4188 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 9, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask04783
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1863 Fin15AnchoredAtom1874 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1900 Fin15AnchoredAtom1903 Fin15AnchoredAtom1915 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1929 Fin15AnchoredAtom1996 Fin15AnchoredAtom1999 Fin15AnchoredAtom2010
    Fin15AnchoredAtom2059 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2149 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2230 Fin15AnchoredAtom2279 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2395 Fin15AnchoredAtom2444 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2838 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2864 Fin15AnchoredAtom2931 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2945 Fin15AnchoredAtom2994 Fin15AnchoredAtom3096 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3110 Fin15AnchoredAtom3159 Fin15AnchoredAtom3363 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3605 Fin15AnchoredAtom3654 Fin15AnchoredAtom3858
    Fin15AnchoredAtom4188 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30577 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2060 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2280 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2445 chi ∧
      ¬Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2995 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom3859 chi ∧
      ¬Fin15AnchoredAtom4189 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 9, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask08879
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1864 Fin15AnchoredAtom1875 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1900 Fin15AnchoredAtom1904 Fin15AnchoredAtom1915 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1930 Fin15AnchoredAtom1996 Fin15AnchoredAtom2000 Fin15AnchoredAtom2011
    Fin15AnchoredAtom2060 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2150 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2231 Fin15AnchoredAtom2280 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2396 Fin15AnchoredAtom2445 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2839 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2865 Fin15AnchoredAtom2931 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2946 Fin15AnchoredAtom2995 Fin15AnchoredAtom3096 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3111 Fin15AnchoredAtom3160 Fin15AnchoredAtom3364 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3606 Fin15AnchoredAtom3655 Fin15AnchoredAtom3859
    Fin15AnchoredAtom4189 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30578 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1860 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1915 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1996 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2061 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2135 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2216 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2281 chi ∧
      ¬Fin15AnchoredAtom2381 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2446 chi ∧
      ¬Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2931 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2996 chi ∧
      ¬Fin15AnchoredAtom3096 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom3591 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom3860 chi ∧
      ¬Fin15AnchoredAtom4190 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 9, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17071
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1826
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1843 Fin15AnchoredAtom1845 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1860 Fin15AnchoredAtom1865 Fin15AnchoredAtom1876 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1900 Fin15AnchoredAtom1905 Fin15AnchoredAtom1915 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1931 Fin15AnchoredAtom1996 Fin15AnchoredAtom2001 Fin15AnchoredAtom2012
    Fin15AnchoredAtom2061 Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2135 Fin15AnchoredAtom2140 Fin15AnchoredAtom2151 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2232 Fin15AnchoredAtom2281 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2397 Fin15AnchoredAtom2446 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2835 Fin15AnchoredAtom2840 Fin15AnchoredAtom2850
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2866 Fin15AnchoredAtom2931 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2947 Fin15AnchoredAtom2996 Fin15AnchoredAtom3096 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3112 Fin15AnchoredAtom3161 Fin15AnchoredAtom3365 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3607 Fin15AnchoredAtom3656 Fin15AnchoredAtom3860
    Fin15AnchoredAtom4190 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30579 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2283 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2448 chi ∧
      ¬Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2998 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom3862 chi ∧
      ¬Fin15AnchoredAtom4192 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05295
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1863 Fin15AnchoredAtom1878 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1903 Fin15AnchoredAtom1916 Fin15AnchoredAtom1918
    Fin15AnchoredAtom1933 Fin15AnchoredAtom1997 Fin15AnchoredAtom1999 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2063 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2153 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2234 Fin15AnchoredAtom2283 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2399 Fin15AnchoredAtom2448 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2853 Fin15AnchoredAtom2868 Fin15AnchoredAtom2932 Fin15AnchoredAtom2934
    Fin15AnchoredAtom2949 Fin15AnchoredAtom2998 Fin15AnchoredAtom3097 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3163 Fin15AnchoredAtom3367 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3609 Fin15AnchoredAtom3658 Fin15AnchoredAtom3862
    Fin15AnchoredAtom4192 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30580 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2284 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2449 chi ∧
      ¬Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2999 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom3863 chi ∧
      ¬Fin15AnchoredAtom4193 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09391
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1864 Fin15AnchoredAtom1879 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1904 Fin15AnchoredAtom1916 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1934 Fin15AnchoredAtom1997 Fin15AnchoredAtom2000 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2064 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2154 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2235 Fin15AnchoredAtom2284 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2400 Fin15AnchoredAtom2449 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2869 Fin15AnchoredAtom2932 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2950 Fin15AnchoredAtom2999 Fin15AnchoredAtom3097 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3164 Fin15AnchoredAtom3368 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3610 Fin15AnchoredAtom3659 Fin15AnchoredAtom3863
    Fin15AnchoredAtom4193 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30581 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1916 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom1997 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2136 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2217 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2285 chi ∧
      ¬Fin15AnchoredAtom2382 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2450 chi ∧
      ¬Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2932 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom3000 chi ∧
      ¬Fin15AnchoredAtom3097 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom3592 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom3864 chi ∧
      ¬Fin15AnchoredAtom4194 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17583
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1843 Fin15AnchoredAtom1846 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1861 Fin15AnchoredAtom1865 Fin15AnchoredAtom1880 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1905 Fin15AnchoredAtom1916 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1935 Fin15AnchoredAtom1997 Fin15AnchoredAtom2001 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2065 Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2136 Fin15AnchoredAtom2140 Fin15AnchoredAtom2155 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2236 Fin15AnchoredAtom2285 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2401 Fin15AnchoredAtom2450 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2836 Fin15AnchoredAtom2840 Fin15AnchoredAtom2851
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2870 Fin15AnchoredAtom2932 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2951 Fin15AnchoredAtom3000 Fin15AnchoredAtom3097 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3165 Fin15AnchoredAtom3369 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3611 Fin15AnchoredAtom3660 Fin15AnchoredAtom3864
    Fin15AnchoredAtom4194 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30582 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2289 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2454 chi ∧
      ¬Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3004 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom3868 chi ∧
      ¬Fin15AnchoredAtom4198 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12463
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1843 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1864 Fin15AnchoredAtom1884 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1904 Fin15AnchoredAtom1918 Fin15AnchoredAtom1919
    Fin15AnchoredAtom1939 Fin15AnchoredAtom1999 Fin15AnchoredAtom2000 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2069 Fin15AnchoredAtom2118 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2159 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2240 Fin15AnchoredAtom2289 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2405 Fin15AnchoredAtom2454 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2854 Fin15AnchoredAtom2874 Fin15AnchoredAtom2934 Fin15AnchoredAtom2935
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3004 Fin15AnchoredAtom3099 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3169 Fin15AnchoredAtom3373 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3615 Fin15AnchoredAtom3664 Fin15AnchoredAtom3868
    Fin15AnchoredAtom4198 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30583 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1918 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom1999 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2138 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2219 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2290 chi ∧
      ¬Fin15AnchoredAtom2384 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2455 chi ∧
      ¬Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2934 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom3005 chi ∧
      ¬Fin15AnchoredAtom3099 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom3869 chi ∧
      ¬Fin15AnchoredAtom4199 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask20655
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1843 Fin15AnchoredAtom1848 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1863 Fin15AnchoredAtom1865 Fin15AnchoredAtom1885 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1905 Fin15AnchoredAtom1918 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1940 Fin15AnchoredAtom1999 Fin15AnchoredAtom2001 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2070 Fin15AnchoredAtom2118 Fin15AnchoredAtom2123 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2138 Fin15AnchoredAtom2140 Fin15AnchoredAtom2160 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2241 Fin15AnchoredAtom2290 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2406 Fin15AnchoredAtom2455 Fin15AnchoredAtom2659
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2838 Fin15AnchoredAtom2840 Fin15AnchoredAtom2853
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2875 Fin15AnchoredAtom2934 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3005 Fin15AnchoredAtom3099 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3170 Fin15AnchoredAtom3374 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3616 Fin15AnchoredAtom3665 Fin15AnchoredAtom3869
    Fin15AnchoredAtom4199 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30584 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1824 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1843 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1919 chi ∧
      ¬Fin15AnchoredAtom1920 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2000 chi ∧
      ¬Fin15AnchoredAtom2001 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom2118 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2139 chi ∧
      ¬Fin15AnchoredAtom2140 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2220 chi ∧
      ¬Fin15AnchoredAtom2221 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2291 chi ∧
      ¬Fin15AnchoredAtom2385 chi ∧
      ¬Fin15AnchoredAtom2386 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2456 chi ∧
      ¬Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2935 chi ∧
      ¬Fin15AnchoredAtom2936 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3006 chi ∧
      ¬Fin15AnchoredAtom3100 chi ∧
      ¬Fin15AnchoredAtom3101 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom3870 chi ∧
      ¬Fin15AnchoredAtom4200 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 7, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask24751
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1824 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1843 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1864 Fin15AnchoredAtom1865 Fin15AnchoredAtom1886 Fin15AnchoredAtom1898
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1905 Fin15AnchoredAtom1919 Fin15AnchoredAtom1920
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2000 Fin15AnchoredAtom2001 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2071 Fin15AnchoredAtom2118 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2139 Fin15AnchoredAtom2140 Fin15AnchoredAtom2161 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2242 Fin15AnchoredAtom2291 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2407 Fin15AnchoredAtom2456 Fin15AnchoredAtom2660
    Fin15AnchoredAtom2833 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840 Fin15AnchoredAtom2854
    Fin15AnchoredAtom2855 Fin15AnchoredAtom2876 Fin15AnchoredAtom2935 Fin15AnchoredAtom2936
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3006 Fin15AnchoredAtom3100 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3171 Fin15AnchoredAtom3375 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3617 Fin15AnchoredAtom3666 Fin15AnchoredAtom3870
    Fin15AnchoredAtom4200 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30585 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2308 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom3023 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom3887 chi ∧
      ¬Fin15AnchoredAtom4217 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 9, 10, 12}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask05679
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1829 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1874 Fin15AnchoredAtom1878 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1903 Fin15AnchoredAtom1927 Fin15AnchoredAtom1929
    Fin15AnchoredAtom1933 Fin15AnchoredAtom2008 Fin15AnchoredAtom2010 Fin15AnchoredAtom2014
    Fin15AnchoredAtom2088 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2234 Fin15AnchoredAtom2308 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2399 Fin15AnchoredAtom2473 Fin15AnchoredAtom2677
    Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2838 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2864 Fin15AnchoredAtom2868 Fin15AnchoredAtom2943 Fin15AnchoredAtom2945
    Fin15AnchoredAtom2949 Fin15AnchoredAtom3023 Fin15AnchoredAtom3108 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3114 Fin15AnchoredAtom3188 Fin15AnchoredAtom3392 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3609 Fin15AnchoredAtom3683 Fin15AnchoredAtom3887
    Fin15AnchoredAtom4217 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30586 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2309 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom3024 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom3888 chi ∧
      ¬Fin15AnchoredAtom4218 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 9, 10, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask09775
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1875 Fin15AnchoredAtom1879 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1904 Fin15AnchoredAtom1927 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1934 Fin15AnchoredAtom2008 Fin15AnchoredAtom2011 Fin15AnchoredAtom2015
    Fin15AnchoredAtom2089 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2235 Fin15AnchoredAtom2309 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2400 Fin15AnchoredAtom2474 Fin15AnchoredAtom2678
    Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2839 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2869 Fin15AnchoredAtom2943 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2950 Fin15AnchoredAtom3024 Fin15AnchoredAtom3108 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3115 Fin15AnchoredAtom3189 Fin15AnchoredAtom3393 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3610 Fin15AnchoredAtom3684 Fin15AnchoredAtom3888
    Fin15AnchoredAtom4218 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30587 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1927 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1935 chi ∧
      ¬Fin15AnchoredAtom2008 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2016 chi ∧
      ¬Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2147 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2155 chi ∧
      ¬Fin15AnchoredAtom2228 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2236 chi ∧
      ¬Fin15AnchoredAtom2310 chi ∧
      ¬Fin15AnchoredAtom2393 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2401 chi ∧
      ¬Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom2943 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2951 chi ∧
      ¬Fin15AnchoredAtom3025 chi ∧
      ¬Fin15AnchoredAtom3108 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3116 chi ∧
      ¬Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom3889 chi ∧
      ¬Fin15AnchoredAtom4219 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 9, 10, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask17967
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1826 Fin15AnchoredAtom1827
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1845 Fin15AnchoredAtom1846 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1872 Fin15AnchoredAtom1876 Fin15AnchoredAtom1880 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1901 Fin15AnchoredAtom1905 Fin15AnchoredAtom1927 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1935 Fin15AnchoredAtom2008 Fin15AnchoredAtom2012 Fin15AnchoredAtom2016
    Fin15AnchoredAtom2090 Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2232 Fin15AnchoredAtom2236 Fin15AnchoredAtom2310 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2401 Fin15AnchoredAtom2475 Fin15AnchoredAtom2679
    Fin15AnchoredAtom2835 Fin15AnchoredAtom2836 Fin15AnchoredAtom2840 Fin15AnchoredAtom2862
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2870 Fin15AnchoredAtom2943 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2951 Fin15AnchoredAtom3025 Fin15AnchoredAtom3108 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3190 Fin15AnchoredAtom3394 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3611 Fin15AnchoredAtom3685 Fin15AnchoredAtom3889
    Fin15AnchoredAtom4219 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30588 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2094 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2314 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3029 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom3893 chi ∧
      ¬Fin15AnchoredAtom4223 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 9, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask12847
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1826 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1875 Fin15AnchoredAtom1884 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1904 Fin15AnchoredAtom1929 Fin15AnchoredAtom1930
    Fin15AnchoredAtom1939 Fin15AnchoredAtom2010 Fin15AnchoredAtom2011 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2094 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2240 Fin15AnchoredAtom2314 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2405 Fin15AnchoredAtom2479 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2835 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2865 Fin15AnchoredAtom2874 Fin15AnchoredAtom2945 Fin15AnchoredAtom2946
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3029 Fin15AnchoredAtom3110 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3194 Fin15AnchoredAtom3398 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3615 Fin15AnchoredAtom3689 Fin15AnchoredAtom3893
    Fin15AnchoredAtom4223 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30589 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1929 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1940 chi ∧
      ¬Fin15AnchoredAtom2010 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2021 chi ∧
      ¬Fin15AnchoredAtom2095 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2149 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2160 chi ∧
      ¬Fin15AnchoredAtom2230 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2241 chi ∧
      ¬Fin15AnchoredAtom2315 chi ∧
      ¬Fin15AnchoredAtom2395 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2406 chi ∧
      ¬Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom2945 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2956 chi ∧
      ¬Fin15AnchoredAtom3030 chi ∧
      ¬Fin15AnchoredAtom3110 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3121 chi ∧
      ¬Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom3894 chi ∧
      ¬Fin15AnchoredAtom4224 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 9, 12, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask21039
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1826 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1845 Fin15AnchoredAtom1848 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1874 Fin15AnchoredAtom1876 Fin15AnchoredAtom1885 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1905 Fin15AnchoredAtom1929 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1940 Fin15AnchoredAtom2010 Fin15AnchoredAtom2012 Fin15AnchoredAtom2021
    Fin15AnchoredAtom2095 Fin15AnchoredAtom2120 Fin15AnchoredAtom2123 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2232 Fin15AnchoredAtom2241 Fin15AnchoredAtom2315 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2406 Fin15AnchoredAtom2480 Fin15AnchoredAtom2684
    Fin15AnchoredAtom2835 Fin15AnchoredAtom2838 Fin15AnchoredAtom2840 Fin15AnchoredAtom2864
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2875 Fin15AnchoredAtom2945 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2956 Fin15AnchoredAtom3030 Fin15AnchoredAtom3110 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3195 Fin15AnchoredAtom3399 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3616 Fin15AnchoredAtom3690 Fin15AnchoredAtom3894
    Fin15AnchoredAtom4224 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30590 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1826 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1831 chi ∧
      ¬Fin15AnchoredAtom1845 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1850 chi ∧
      ¬Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom1930 chi ∧
      ¬Fin15AnchoredAtom1931 chi ∧
      ¬Fin15AnchoredAtom1941 chi ∧
      ¬Fin15AnchoredAtom2011 chi ∧
      ¬Fin15AnchoredAtom2012 chi ∧
      ¬Fin15AnchoredAtom2022 chi ∧
      ¬Fin15AnchoredAtom2096 chi ∧
      ¬Fin15AnchoredAtom2120 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2125 chi ∧
      ¬Fin15AnchoredAtom2150 chi ∧
      ¬Fin15AnchoredAtom2151 chi ∧
      ¬Fin15AnchoredAtom2161 chi ∧
      ¬Fin15AnchoredAtom2231 chi ∧
      ¬Fin15AnchoredAtom2232 chi ∧
      ¬Fin15AnchoredAtom2242 chi ∧
      ¬Fin15AnchoredAtom2316 chi ∧
      ¬Fin15AnchoredAtom2396 chi ∧
      ¬Fin15AnchoredAtom2397 chi ∧
      ¬Fin15AnchoredAtom2407 chi ∧
      ¬Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom2946 chi ∧
      ¬Fin15AnchoredAtom2947 chi ∧
      ¬Fin15AnchoredAtom2957 chi ∧
      ¬Fin15AnchoredAtom3031 chi ∧
      ¬Fin15AnchoredAtom3111 chi ∧
      ¬Fin15AnchoredAtom3112 chi ∧
      ¬Fin15AnchoredAtom3122 chi ∧
      ¬Fin15AnchoredAtom3196 chi ∧
      ¬Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom3895 chi ∧
      ¬Fin15AnchoredAtom4225 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 9, 13, 14}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask25135
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1826 Fin15AnchoredAtom1830
    Fin15AnchoredAtom1831 Fin15AnchoredAtom1845 Fin15AnchoredAtom1849 Fin15AnchoredAtom1850
    Fin15AnchoredAtom1875 Fin15AnchoredAtom1876 Fin15AnchoredAtom1886 Fin15AnchoredAtom1900
    Fin15AnchoredAtom1904 Fin15AnchoredAtom1905 Fin15AnchoredAtom1930 Fin15AnchoredAtom1931
    Fin15AnchoredAtom1941 Fin15AnchoredAtom2011 Fin15AnchoredAtom2012 Fin15AnchoredAtom2022
    Fin15AnchoredAtom2096 Fin15AnchoredAtom2120 Fin15AnchoredAtom2124 Fin15AnchoredAtom2125
    Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2232 Fin15AnchoredAtom2242 Fin15AnchoredAtom2316 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2407 Fin15AnchoredAtom2481 Fin15AnchoredAtom2685
    Fin15AnchoredAtom2835 Fin15AnchoredAtom2839 Fin15AnchoredAtom2840 Fin15AnchoredAtom2865
    Fin15AnchoredAtom2866 Fin15AnchoredAtom2876 Fin15AnchoredAtom2946 Fin15AnchoredAtom2947
    Fin15AnchoredAtom2957 Fin15AnchoredAtom3031 Fin15AnchoredAtom3111 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3196 Fin15AnchoredAtom3400 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3617 Fin15AnchoredAtom3691 Fin15AnchoredAtom3895
    Fin15AnchoredAtom4225 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

theorem fin15Anchored_clause30591 (chi : TripleColoring 15)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(¬Fin15AnchoredAtom1822 chi ∧
      ¬Fin15AnchoredAtom1827 chi ∧
      ¬Fin15AnchoredAtom1829 chi ∧
      ¬Fin15AnchoredAtom1830 chi ∧
      ¬Fin15AnchoredAtom1846 chi ∧
      ¬Fin15AnchoredAtom1848 chi ∧
      ¬Fin15AnchoredAtom1849 chi ∧
      ¬Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom1933 chi ∧
      ¬Fin15AnchoredAtom1934 chi ∧
      ¬Fin15AnchoredAtom1939 chi ∧
      ¬Fin15AnchoredAtom2014 chi ∧
      ¬Fin15AnchoredAtom2015 chi ∧
      ¬Fin15AnchoredAtom2020 chi ∧
      ¬Fin15AnchoredAtom2100 chi ∧
      ¬Fin15AnchoredAtom2121 chi ∧
      ¬Fin15AnchoredAtom2123 chi ∧
      ¬Fin15AnchoredAtom2124 chi ∧
      ¬Fin15AnchoredAtom2153 chi ∧
      ¬Fin15AnchoredAtom2154 chi ∧
      ¬Fin15AnchoredAtom2159 chi ∧
      ¬Fin15AnchoredAtom2234 chi ∧
      ¬Fin15AnchoredAtom2235 chi ∧
      ¬Fin15AnchoredAtom2240 chi ∧
      ¬Fin15AnchoredAtom2320 chi ∧
      ¬Fin15AnchoredAtom2399 chi ∧
      ¬Fin15AnchoredAtom2400 chi ∧
      ¬Fin15AnchoredAtom2405 chi ∧
      ¬Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom2949 chi ∧
      ¬Fin15AnchoredAtom2950 chi ∧
      ¬Fin15AnchoredAtom2955 chi ∧
      ¬Fin15AnchoredAtom3035 chi ∧
      ¬Fin15AnchoredAtom3114 chi ∧
      ¬Fin15AnchoredAtom3115 chi ∧
      ¬Fin15AnchoredAtom3120 chi ∧
      ¬Fin15AnchoredAtom3200 chi ∧
      ¬Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom3899 chi ∧
      ¬Fin15AnchoredAtom4229 chi) := by
  intro hbad
  apply hno
  refine ⟨{0, 1, 2, 3, 5, 10, 12, 13}, by decide, ?_⟩
  rintro ⟨polygon, hsubset, hcard, hstrong⟩
  have heq := fin15Anchored_fiveSubset_mask13359
    polygon hsubset hcard
  unfold Fin15AnchoredAtom1822 Fin15AnchoredAtom1827 Fin15AnchoredAtom1829
    Fin15AnchoredAtom1830 Fin15AnchoredAtom1846 Fin15AnchoredAtom1848 Fin15AnchoredAtom1849
    Fin15AnchoredAtom1878 Fin15AnchoredAtom1879 Fin15AnchoredAtom1884 Fin15AnchoredAtom1901
    Fin15AnchoredAtom1903 Fin15AnchoredAtom1904 Fin15AnchoredAtom1933 Fin15AnchoredAtom1934
    Fin15AnchoredAtom1939 Fin15AnchoredAtom2014 Fin15AnchoredAtom2015 Fin15AnchoredAtom2020
    Fin15AnchoredAtom2100 Fin15AnchoredAtom2121 Fin15AnchoredAtom2123 Fin15AnchoredAtom2124
    Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2240 Fin15AnchoredAtom2320 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2405 Fin15AnchoredAtom2485 Fin15AnchoredAtom2689
    Fin15AnchoredAtom2836 Fin15AnchoredAtom2838 Fin15AnchoredAtom2839 Fin15AnchoredAtom2868
    Fin15AnchoredAtom2869 Fin15AnchoredAtom2874 Fin15AnchoredAtom2949 Fin15AnchoredAtom2950
    Fin15AnchoredAtom2955 Fin15AnchoredAtom3035 Fin15AnchoredAtom3114 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3200 Fin15AnchoredAtom3404 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3615 Fin15AnchoredAtom3695 Fin15AnchoredAtom3899
    Fin15AnchoredAtom4229 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34, n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48, n49, n50, n51, n52, n53, n54, n55⟩ := hbad
  rcases heq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hstrong n55
  · exact absurd hstrong n54
  · exact absurd hstrong n53
  · exact absurd hstrong n52
  · exact absurd hstrong n51
  · exact absurd hstrong n50
  · exact absurd hstrong n49
  · exact absurd hstrong n48
  · exact absurd hstrong n47
  · exact absurd hstrong n46
  · exact absurd hstrong n45
  · exact absurd hstrong n44
  · exact absurd hstrong n43
  · exact absurd hstrong n42
  · exact absurd hstrong n41
  · exact absurd hstrong n40
  · exact absurd hstrong n39
  · exact absurd hstrong n38
  · exact absurd hstrong n37
  · exact absurd hstrong n36
  · exact absurd hstrong n35
  · exact absurd hstrong n34
  · exact absurd hstrong n33
  · exact absurd hstrong n32
  · exact absurd hstrong n31
  · exact absurd hstrong n30
  · exact absurd hstrong n29
  · exact absurd hstrong n28
  · exact absurd hstrong n27
  · exact absurd hstrong n26
  · exact absurd hstrong n25
  · exact absurd hstrong n24
  · exact absurd hstrong n23
  · exact absurd hstrong n22
  · exact absurd hstrong n21
  · exact absurd hstrong n20
  · exact absurd hstrong n19
  · exact absurd hstrong n18
  · exact absurd hstrong n17
  · exact absurd hstrong n16
  · exact absurd hstrong n15
  · exact absurd hstrong n14
  · exact absurd hstrong n13
  · exact absurd hstrong n12
  · exact absurd hstrong n11
  · exact absurd hstrong n10
  · exact absurd hstrong n9
  · exact absurd hstrong n8
  · exact absurd hstrong n7
  · exact absurd hstrong n6
  · exact absurd hstrong n5
  · exact absurd hstrong n4
  · exact absurd hstrong n3
  · exact absurd hstrong n2
  · exact absurd hstrong n1
  · exact absurd hstrong n0

end ErdosSzekeres

end
