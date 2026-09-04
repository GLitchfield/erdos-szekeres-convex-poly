module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 228. -/

theorem fin15Anchored_clause29184 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom4506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2556 Fin15AnchoredAtom2561 Fin15AnchoredAtom2566
    Fin15AnchoredAtom2581 Fin15AnchoredAtom2756 Fin15AnchoredAtom4506 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 9, 14}, {0, 7, 8, 9, 14}, {0, 4, 8, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29185 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom4508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2557 Fin15AnchoredAtom2559 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2583 Fin15AnchoredAtom2758 Fin15AnchoredAtom4508 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 10, 12}, {0, 7, 8, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29186 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom4509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2557 Fin15AnchoredAtom2560 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2584 Fin15AnchoredAtom2759 Fin15AnchoredAtom4509 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 10, 13}, {0, 7, 8, 10, 13}, {0, 4, 8, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 8, 13}, {0, 4, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29187 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom4515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2559 Fin15AnchoredAtom2561 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2590 Fin15AnchoredAtom2765 Fin15AnchoredAtom4515 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 12, 14}, {0, 7, 8, 12, 14}, {0, 4, 8, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 8, 14}, {0, 4, 7, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29188 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom4518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2562 Fin15AnchoredAtom2564 Fin15AnchoredAtom2568
    Fin15AnchoredAtom2593 Fin15AnchoredAtom2768 Fin15AnchoredAtom4518 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29189 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom4519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2562 Fin15AnchoredAtom2565 Fin15AnchoredAtom2569
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2769 Fin15AnchoredAtom4519 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29190 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom4520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2562 Fin15AnchoredAtom2566 Fin15AnchoredAtom2570
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2770 Fin15AnchoredAtom4520 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29191 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom4524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2564 Fin15AnchoredAtom2565 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2599 Fin15AnchoredAtom2774 Fin15AnchoredAtom4524 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 9, 13}, {0, 4, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29192 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom4525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2564 Fin15AnchoredAtom2566 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2775 Fin15AnchoredAtom4525 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29193 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom4526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2565 Fin15AnchoredAtom2566 Fin15AnchoredAtom2576
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2776 Fin15AnchoredAtom4526 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 13, 14}, {0, 7, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 9, 14}, {0, 4, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29194 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2567 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2571 chi ∧
      Fin15AnchoredAtom2602 chi ∧
      Fin15AnchoredAtom2777 chi ∧
      Fin15AnchoredAtom4527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2567 Fin15AnchoredAtom2568 Fin15AnchoredAtom2571
    Fin15AnchoredAtom2602 Fin15AnchoredAtom2777 Fin15AnchoredAtom4527 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 11, 12}, {0, 7, 10, 11, 12}, {0, 4, 10, 11, 12}, {0, 4, 7, 11, 12}, {0, 4, 7, 10, 12}, {0, 4, 7, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29195 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom4530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2568 Fin15AnchoredAtom2569 Fin15AnchoredAtom2574
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2780 Fin15AnchoredAtom4530 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 7, 10, 13}, {0, 4, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29196 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom4531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2568 Fin15AnchoredAtom2570 Fin15AnchoredAtom2575
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2781 Fin15AnchoredAtom4531 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29197 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom4532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2569 Fin15AnchoredAtom2570 Fin15AnchoredAtom2576
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2782 Fin15AnchoredAtom4532 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 10, 14}, {0, 4, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29198 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom4536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2574 Fin15AnchoredAtom2575 Fin15AnchoredAtom2576
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2786 Fin15AnchoredAtom4536 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 7, 12, 14}, {0, 4, 7, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29199 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2577 Fin15AnchoredAtom2579 Fin15AnchoredAtom2583
    Fin15AnchoredAtom2593 Fin15AnchoredAtom2788 Fin15AnchoredAtom4538 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 10, 12}, {0, 8, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 8, 9, 12}, {0, 4, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29200 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2579 Fin15AnchoredAtom2580 Fin15AnchoredAtom2589
    Fin15AnchoredAtom2599 Fin15AnchoredAtom2794 Fin15AnchoredAtom4544 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 12, 13}, {0, 8, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 9, 13}, {0, 4, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29201 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2579 Fin15AnchoredAtom2581 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2795 Fin15AnchoredAtom4545 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 8, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 12, 14}, {0, 8, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 8, 12, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29202 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2580 Fin15AnchoredAtom2581 Fin15AnchoredAtom2591
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2796 Fin15AnchoredAtom4546 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 13, 14}, {0, 8, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 8, 9, 14}, {0, 4, 8, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29203 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom4550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2583 Fin15AnchoredAtom2584 Fin15AnchoredAtom2589
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2800 Fin15AnchoredAtom4550 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 8, 10, 13}, {0, 4, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29204 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2583 Fin15AnchoredAtom2585 Fin15AnchoredAtom2590
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2801 Fin15AnchoredAtom4551 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 8, 12, 14}, {0, 4, 8, 10, 14}, {0, 4, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29205 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2589 Fin15AnchoredAtom2590 Fin15AnchoredAtom2591
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2806 Fin15AnchoredAtom4556 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 8, 12, 14}, {0, 4, 8, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29206 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2593 Fin15AnchoredAtom2594 Fin15AnchoredAtom2599
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2810 Fin15AnchoredAtom4560 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 13}, {0, 9, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 9, 10, 13}, {0, 4, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29207 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2593 Fin15AnchoredAtom2595 Fin15AnchoredAtom2600
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2811 Fin15AnchoredAtom4561 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 14}, {0, 9, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29208 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2594 Fin15AnchoredAtom2595 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2812 Fin15AnchoredAtom4562 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 13, 14}, {0, 9, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 10, 14}, {0, 4, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29209 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2599 Fin15AnchoredAtom2600 Fin15AnchoredAtom2601
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2816 Fin15AnchoredAtom4566 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 9, 12, 14}, {0, 4, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29210 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2602 chi ∧
      Fin15AnchoredAtom2603 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2608 chi ∧
      Fin15AnchoredAtom2817 chi ∧
      Fin15AnchoredAtom4567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2602 Fin15AnchoredAtom2603 Fin15AnchoredAtom2605
    Fin15AnchoredAtom2608 Fin15AnchoredAtom2817 Fin15AnchoredAtom4567 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 10, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 10, 11, 12, 13}, {0, 10, 11, 12, 13}, {0, 4, 11, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 10, 11, 13}, {0, 4, 10, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29211 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2605 Fin15AnchoredAtom2606 Fin15AnchoredAtom2607
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2820 Fin15AnchoredAtom4570 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 10, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 10, 12, 14}, {0, 4, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29212 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom4578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2613 Fin15AnchoredAtom2614 Fin15AnchoredAtom2625
    Fin15AnchoredAtom2646 Fin15AnchoredAtom2702 Fin15AnchoredAtom4578 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {0, 6, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 6, 9, 10}, {0, 5, 6, 7, 10}, {0, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29213 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom4580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2613 Fin15AnchoredAtom2616 Fin15AnchoredAtom2627
    Fin15AnchoredAtom2648 Fin15AnchoredAtom2704 Fin15AnchoredAtom4580 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {0, 6, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29214 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom4581 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2613 Fin15AnchoredAtom2617 Fin15AnchoredAtom2628
    Fin15AnchoredAtom2649 Fin15AnchoredAtom2705 Fin15AnchoredAtom4581 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {0, 6, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29215 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom4582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2613 Fin15AnchoredAtom2618 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2650 Fin15AnchoredAtom2706 Fin15AnchoredAtom4582 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {0, 6, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29216 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2615 chi ∧
      Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom2707 chi ∧
      Fin15AnchoredAtom4583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2614 Fin15AnchoredAtom2615 Fin15AnchoredAtom2630
    Fin15AnchoredAtom2651 Fin15AnchoredAtom2707 Fin15AnchoredAtom4583 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 11}, {0, 6, 7, 10, 11}, {0, 5, 7, 10, 11}, {0, 5, 6, 10, 11}, {0, 5, 6, 7, 11}, {0, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29217 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom4584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2614 Fin15AnchoredAtom2616 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2652 Fin15AnchoredAtom2708 Fin15AnchoredAtom4584 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {0, 6, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 7, 12}, {0, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29218 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom4585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2614 Fin15AnchoredAtom2617 Fin15AnchoredAtom2632
    Fin15AnchoredAtom2653 Fin15AnchoredAtom2709 Fin15AnchoredAtom4585 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {0, 6, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29219 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom4586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2614 Fin15AnchoredAtom2618 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2654 Fin15AnchoredAtom2710 Fin15AnchoredAtom4586 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {0, 6, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29220 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2615 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2635 chi ∧
      Fin15AnchoredAtom2656 chi ∧
      Fin15AnchoredAtom2712 chi ∧
      Fin15AnchoredAtom4588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2615 Fin15AnchoredAtom2617 Fin15AnchoredAtom2635
    Fin15AnchoredAtom2656 Fin15AnchoredAtom2712 Fin15AnchoredAtom4588 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 11, 13}, {0, 6, 7, 11, 13}, {0, 5, 7, 11, 13}, {0, 5, 6, 11, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29221 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom4590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2616 Fin15AnchoredAtom2617 Fin15AnchoredAtom2637
    Fin15AnchoredAtom2658 Fin15AnchoredAtom2714 Fin15AnchoredAtom4590 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {0, 6, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 7, 13}, {0, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29222 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom4591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2616 Fin15AnchoredAtom2618 Fin15AnchoredAtom2638
    Fin15AnchoredAtom2659 Fin15AnchoredAtom2715 Fin15AnchoredAtom4591 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {0, 6, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29223 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom4592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2617 Fin15AnchoredAtom2618 Fin15AnchoredAtom2639
    Fin15AnchoredAtom2660 Fin15AnchoredAtom2716 Fin15AnchoredAtom4592 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {0, 6, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 7, 14}, {0, 5, 6, 7, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29224 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom4597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2619 Fin15AnchoredAtom2624 Fin15AnchoredAtom2629
    Fin15AnchoredAtom2665 Fin15AnchoredAtom2721 Fin15AnchoredAtom4597 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 14}, {0, 6, 8, 9, 14}, {0, 5, 8, 9, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29225 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2620 chi ∧
      Fin15AnchoredAtom2623 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom4600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2620 Fin15AnchoredAtom2623 Fin15AnchoredAtom2632
    Fin15AnchoredAtom2668 Fin15AnchoredAtom2724 Fin15AnchoredAtom4600 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 13}, {0, 6, 8, 10, 13}, {0, 5, 8, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 8, 13}, {0, 5, 6, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29226 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2622 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom4606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2622 Fin15AnchoredAtom2624 Fin15AnchoredAtom2638
    Fin15AnchoredAtom2674 Fin15AnchoredAtom2730 Fin15AnchoredAtom4606 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 12, 14}, {0, 6, 8, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29227 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2623 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom4607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2623 Fin15AnchoredAtom2624 Fin15AnchoredAtom2639
    Fin15AnchoredAtom2675 Fin15AnchoredAtom2731 Fin15AnchoredAtom4607 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 13, 14}, {0, 6, 8, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 8, 14}, {0, 5, 6, 8, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29228 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom4609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2625 Fin15AnchoredAtom2627 Fin15AnchoredAtom2631
    Fin15AnchoredAtom2677 Fin15AnchoredAtom2733 Fin15AnchoredAtom4609 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29229 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom4610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2625 Fin15AnchoredAtom2628 Fin15AnchoredAtom2632
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2734 Fin15AnchoredAtom4610 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29230 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom4611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2625 Fin15AnchoredAtom2629 Fin15AnchoredAtom2633
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2735 Fin15AnchoredAtom4611 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29231 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2626 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2634 chi ∧
      Fin15AnchoredAtom2680 chi ∧
      Fin15AnchoredAtom2736 chi ∧
      Fin15AnchoredAtom4612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2626 Fin15AnchoredAtom2627 Fin15AnchoredAtom2634
    Fin15AnchoredAtom2680 Fin15AnchoredAtom2736 Fin15AnchoredAtom4612 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 11, 12}, {0, 6, 9, 11, 12}, {0, 5, 9, 11, 12}, {0, 5, 6, 11, 12}, {0, 5, 6, 9, 12}, {0, 5, 6, 9, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29232 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom4615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2627 Fin15AnchoredAtom2628 Fin15AnchoredAtom2637
    Fin15AnchoredAtom2683 Fin15AnchoredAtom2739 Fin15AnchoredAtom4615 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 9, 13}, {0, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29233 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom4616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2627 Fin15AnchoredAtom2629 Fin15AnchoredAtom2638
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2740 Fin15AnchoredAtom4616 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29234 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom4617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2628 Fin15AnchoredAtom2629 Fin15AnchoredAtom2639
    Fin15AnchoredAtom2685 Fin15AnchoredAtom2741 Fin15AnchoredAtom4617 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 9, 14}, {0, 5, 6, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29235 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2634 chi ∧
      Fin15AnchoredAtom2686 chi ∧
      Fin15AnchoredAtom2742 chi ∧
      Fin15AnchoredAtom4618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2630 Fin15AnchoredAtom2631 Fin15AnchoredAtom2634
    Fin15AnchoredAtom2686 Fin15AnchoredAtom2742 Fin15AnchoredAtom4618 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 11, 12}, {0, 6, 10, 11, 12}, {0, 5, 10, 11, 12}, {0, 5, 6, 11, 12}, {0, 5, 6, 10, 12}, {0, 5, 6, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29236 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2636 chi ∧
      Fin15AnchoredAtom2688 chi ∧
      Fin15AnchoredAtom2744 chi ∧
      Fin15AnchoredAtom4620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2630 Fin15AnchoredAtom2633 Fin15AnchoredAtom2636
    Fin15AnchoredAtom2688 Fin15AnchoredAtom2744 Fin15AnchoredAtom4620 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 10, 11, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 10, 11, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 10, 11, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 11, 14}, {0, 6, 10, 11, 14}, {0, 5, 10, 11, 14}, {0, 5, 6, 11, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29237 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom4621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2631 Fin15AnchoredAtom2632 Fin15AnchoredAtom2637
    Fin15AnchoredAtom2689 Fin15AnchoredAtom2745 Fin15AnchoredAtom4621 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 6, 12, 13}, {0, 5, 6, 10, 13}, {0, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29238 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom4622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2631 Fin15AnchoredAtom2633 Fin15AnchoredAtom2638
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2746 Fin15AnchoredAtom4622 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29239 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom4623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2632 Fin15AnchoredAtom2633 Fin15AnchoredAtom2639
    Fin15AnchoredAtom2691 Fin15AnchoredAtom2747 Fin15AnchoredAtom4623 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 10, 14}, {0, 5, 6, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29240 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom4627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2637 Fin15AnchoredAtom2638 Fin15AnchoredAtom2639
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2751 Fin15AnchoredAtom4627 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 6, 13, 14}, {0, 5, 6, 12, 14}, {0, 5, 6, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29241 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom2641 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom4628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2640 Fin15AnchoredAtom2641 Fin15AnchoredAtom2646
    Fin15AnchoredAtom2661 Fin15AnchoredAtom2752 Fin15AnchoredAtom4628 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 10}, {0, 7, 8, 9, 10}, {0, 5, 8, 9, 10}, {0, 5, 7, 9, 10}, {0, 5, 7, 8, 10}, {0, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29242 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom4630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2640 Fin15AnchoredAtom2643 Fin15AnchoredAtom2648
    Fin15AnchoredAtom2663 Fin15AnchoredAtom2754 Fin15AnchoredAtom4630 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 12}, {0, 7, 8, 9, 12}, {0, 5, 8, 9, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 8, 12}, {0, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29243 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom4631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2640 Fin15AnchoredAtom2644 Fin15AnchoredAtom2649
    Fin15AnchoredAtom2664 Fin15AnchoredAtom2755 Fin15AnchoredAtom4631 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 13}, {0, 7, 8, 9, 13}, {0, 5, 8, 9, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29244 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom4632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2640 Fin15AnchoredAtom2645 Fin15AnchoredAtom2650
    Fin15AnchoredAtom2665 Fin15AnchoredAtom2756 Fin15AnchoredAtom4632 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 14}, {0, 7, 8, 9, 14}, {0, 5, 8, 9, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29245 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom4640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2643 Fin15AnchoredAtom2644 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2673 Fin15AnchoredAtom2764 Fin15AnchoredAtom4640 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 12, 13}, {0, 7, 8, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 8, 13}, {0, 5, 7, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29246 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom4641 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2643 Fin15AnchoredAtom2645 Fin15AnchoredAtom2659
    Fin15AnchoredAtom2674 Fin15AnchoredAtom2765 Fin15AnchoredAtom4641 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 12, 14}, {0, 7, 8, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29247 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom4642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2644 Fin15AnchoredAtom2645 Fin15AnchoredAtom2660
    Fin15AnchoredAtom2675 Fin15AnchoredAtom2766 Fin15AnchoredAtom4642 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 13, 14}, {0, 7, 8, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 8, 14}, {0, 5, 7, 8, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29248 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom4644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2646 Fin15AnchoredAtom2648 Fin15AnchoredAtom2652
    Fin15AnchoredAtom2677 Fin15AnchoredAtom2768 Fin15AnchoredAtom4644 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 9, 12}, {0, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29249 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom4645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2646 Fin15AnchoredAtom2649 Fin15AnchoredAtom2653
    Fin15AnchoredAtom2678 Fin15AnchoredAtom2769 Fin15AnchoredAtom4645 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29250 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom4646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2646 Fin15AnchoredAtom2650 Fin15AnchoredAtom2654
    Fin15AnchoredAtom2679 Fin15AnchoredAtom2770 Fin15AnchoredAtom4646 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29251 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom4650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2648 Fin15AnchoredAtom2649 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2683 Fin15AnchoredAtom2774 Fin15AnchoredAtom4650 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 9, 13}, {0, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29252 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom4651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2648 Fin15AnchoredAtom2650 Fin15AnchoredAtom2659
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2775 Fin15AnchoredAtom4651 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29253 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom4652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2649 Fin15AnchoredAtom2650 Fin15AnchoredAtom2660
    Fin15AnchoredAtom2685 Fin15AnchoredAtom2776 Fin15AnchoredAtom4652 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {0, 7, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 9, 14}, {0, 5, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29254 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2655 chi ∧
      Fin15AnchoredAtom2686 chi ∧
      Fin15AnchoredAtom2777 chi ∧
      Fin15AnchoredAtom4653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2651 Fin15AnchoredAtom2652 Fin15AnchoredAtom2655
    Fin15AnchoredAtom2686 Fin15AnchoredAtom2777 Fin15AnchoredAtom4653 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 11, 12}, {0, 7, 10, 11, 12}, {0, 5, 10, 11, 12}, {0, 5, 7, 11, 12}, {0, 5, 7, 10, 12}, {0, 5, 7, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29255 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2656 chi ∧
      Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom2778 chi ∧
      Fin15AnchoredAtom4654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2651 Fin15AnchoredAtom2653 Fin15AnchoredAtom2656
    Fin15AnchoredAtom2687 Fin15AnchoredAtom2778 Fin15AnchoredAtom4654 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 10, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 11, 13}, {0, 7, 10, 11, 13}, {0, 5, 10, 11, 13}, {0, 5, 7, 11, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29256 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom4656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2652 Fin15AnchoredAtom2653 Fin15AnchoredAtom2658
    Fin15AnchoredAtom2689 Fin15AnchoredAtom2780 Fin15AnchoredAtom4656 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 7, 12, 13}, {0, 5, 7, 10, 13}, {0, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29257 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom4657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2652 Fin15AnchoredAtom2654 Fin15AnchoredAtom2659
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2781 Fin15AnchoredAtom4657 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29258 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom4658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2653 Fin15AnchoredAtom2654 Fin15AnchoredAtom2660
    Fin15AnchoredAtom2691 Fin15AnchoredAtom2782 Fin15AnchoredAtom4658 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 10, 14}, {0, 5, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29259 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom4662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2658 Fin15AnchoredAtom2659 Fin15AnchoredAtom2660
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2786 Fin15AnchoredAtom4662 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 7, 13, 14}, {0, 5, 7, 12, 14}, {0, 5, 7, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29260 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2661 Fin15AnchoredAtom2663 Fin15AnchoredAtom2667
    Fin15AnchoredAtom2677 Fin15AnchoredAtom2788 Fin15AnchoredAtom4664 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 12}, {0, 8, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 5, 8, 10, 12}, {0, 5, 8, 9, 12}, {0, 5, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29261 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2663 Fin15AnchoredAtom2664 Fin15AnchoredAtom2673
    Fin15AnchoredAtom2683 Fin15AnchoredAtom2794 Fin15AnchoredAtom4670 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 12, 13}, {0, 8, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 8, 12, 13}, {0, 5, 8, 9, 13}, {0, 5, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29262 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2663 Fin15AnchoredAtom2665 Fin15AnchoredAtom2674
    Fin15AnchoredAtom2684 Fin15AnchoredAtom2795 Fin15AnchoredAtom4671 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 8, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 12, 14}, {0, 8, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29263 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2664 Fin15AnchoredAtom2665 Fin15AnchoredAtom2675
    Fin15AnchoredAtom2685 Fin15AnchoredAtom2796 Fin15AnchoredAtom4672 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 13, 14}, {0, 8, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 9, 14}, {0, 5, 8, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29264 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom2669 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2667 Fin15AnchoredAtom2669 Fin15AnchoredAtom2674
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2801 Fin15AnchoredAtom4677 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29265 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom2669 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom4678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2668 Fin15AnchoredAtom2669 Fin15AnchoredAtom2675
    Fin15AnchoredAtom2691 Fin15AnchoredAtom2802 Fin15AnchoredAtom4678 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 10, 14}, {0, 5, 8, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29266 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2673 Fin15AnchoredAtom2674 Fin15AnchoredAtom2675
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2806 Fin15AnchoredAtom4682 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 8, 13, 14}, {0, 5, 8, 12, 14}, {0, 5, 8, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29267 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2677 Fin15AnchoredAtom2678 Fin15AnchoredAtom2683
    Fin15AnchoredAtom2689 Fin15AnchoredAtom2810 Fin15AnchoredAtom4686 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {0, 9, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 5, 9, 12, 13}, {0, 5, 9, 10, 13}, {0, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29268 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2677 Fin15AnchoredAtom2679 Fin15AnchoredAtom2684
    Fin15AnchoredAtom2690 Fin15AnchoredAtom2811 Fin15AnchoredAtom4687 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {0, 9, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29269 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2678 Fin15AnchoredAtom2679 Fin15AnchoredAtom2685
    Fin15AnchoredAtom2691 Fin15AnchoredAtom2812 Fin15AnchoredAtom4688 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {0, 9, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 10, 14}, {0, 5, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29270 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2683 Fin15AnchoredAtom2684 Fin15AnchoredAtom2685
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2816 Fin15AnchoredAtom4692 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 9, 13, 14}, {0, 5, 9, 12, 14}, {0, 5, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29271 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2689 Fin15AnchoredAtom2690 Fin15AnchoredAtom2691
    Fin15AnchoredAtom2695 Fin15AnchoredAtom2820 Fin15AnchoredAtom4696 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 5, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 5, 10, 13, 14}, {0, 5, 10, 12, 14}, {0, 5, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29272 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom4698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2696 Fin15AnchoredAtom2697 Fin15AnchoredAtom2702
    Fin15AnchoredAtom2717 Fin15AnchoredAtom2752 Fin15AnchoredAtom4698 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 10}, {0, 7, 8, 9, 10}, {0, 6, 8, 9, 10}, {0, 6, 7, 9, 10}, {0, 6, 7, 8, 10}, {0, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29273 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom4701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2696 Fin15AnchoredAtom2700 Fin15AnchoredAtom2705
    Fin15AnchoredAtom2720 Fin15AnchoredAtom2755 Fin15AnchoredAtom4701 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 13}, {0, 7, 8, 9, 13}, {0, 6, 8, 9, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 8, 13}, {0, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29274 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom4702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2696 Fin15AnchoredAtom2701 Fin15AnchoredAtom2706
    Fin15AnchoredAtom2721 Fin15AnchoredAtom2756 Fin15AnchoredAtom4702 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 14}, {0, 7, 8, 9, 14}, {0, 6, 8, 9, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29275 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom2699 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom4704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2697 Fin15AnchoredAtom2699 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2723 Fin15AnchoredAtom2758 Fin15AnchoredAtom4704 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 12}, {0, 7, 8, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 8, 12}, {0, 6, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29276 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom4706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2697 Fin15AnchoredAtom2701 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2725 Fin15AnchoredAtom2760 Fin15AnchoredAtom4706 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 14}, {0, 7, 8, 10, 14}, {0, 6, 8, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29277 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom4712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2700 Fin15AnchoredAtom2701 Fin15AnchoredAtom2716
    Fin15AnchoredAtom2731 Fin15AnchoredAtom2766 Fin15AnchoredAtom4712 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 13, 14}, {0, 7, 8, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 8, 14}, {0, 6, 7, 8, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29278 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom4714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2702 Fin15AnchoredAtom2704 Fin15AnchoredAtom2708
    Fin15AnchoredAtom2733 Fin15AnchoredAtom2768 Fin15AnchoredAtom4714 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 7, 10, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29279 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom4715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2702 Fin15AnchoredAtom2705 Fin15AnchoredAtom2709
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2769 Fin15AnchoredAtom4715 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29280 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom4716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2702 Fin15AnchoredAtom2706 Fin15AnchoredAtom2710
    Fin15AnchoredAtom2735 Fin15AnchoredAtom2770 Fin15AnchoredAtom4716 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29281 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2703 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom2711 chi ∧
      Fin15AnchoredAtom2736 chi ∧
      Fin15AnchoredAtom2771 chi ∧
      Fin15AnchoredAtom4717 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2703 Fin15AnchoredAtom2704 Fin15AnchoredAtom2711
    Fin15AnchoredAtom2736 Fin15AnchoredAtom2771 Fin15AnchoredAtom4717 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 11, 12}, {0, 7, 9, 11, 12}, {0, 6, 9, 11, 12}, {0, 6, 7, 11, 12}, {0, 6, 7, 9, 12}, {0, 6, 7, 9, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29282 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom4720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2704 Fin15AnchoredAtom2705 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2739 Fin15AnchoredAtom2774 Fin15AnchoredAtom4720 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 9, 13}, {0, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29283 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom4721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2704 Fin15AnchoredAtom2706 Fin15AnchoredAtom2715
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2775 Fin15AnchoredAtom4721 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29284 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom4722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2705 Fin15AnchoredAtom2706 Fin15AnchoredAtom2716
    Fin15AnchoredAtom2741 Fin15AnchoredAtom2776 Fin15AnchoredAtom4722 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {0, 7, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 9, 14}, {0, 6, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29285 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom4726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2708 Fin15AnchoredAtom2709 Fin15AnchoredAtom2714
    Fin15AnchoredAtom2745 Fin15AnchoredAtom2780 Fin15AnchoredAtom4726 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 7, 12, 13}, {0, 6, 7, 10, 13}, {0, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29286 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom4727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2708 Fin15AnchoredAtom2710 Fin15AnchoredAtom2715
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2781 Fin15AnchoredAtom4727 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29287 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom4728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2709 Fin15AnchoredAtom2710 Fin15AnchoredAtom2716
    Fin15AnchoredAtom2747 Fin15AnchoredAtom2782 Fin15AnchoredAtom4728 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 10, 14}, {0, 6, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29288 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom4732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2714 Fin15AnchoredAtom2715 Fin15AnchoredAtom2716
    Fin15AnchoredAtom2751 Fin15AnchoredAtom2786 Fin15AnchoredAtom4732 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 7, 13, 14}, {0, 6, 7, 12, 14}, {0, 6, 7, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29289 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2717 Fin15AnchoredAtom2719 Fin15AnchoredAtom2723
    Fin15AnchoredAtom2733 Fin15AnchoredAtom2788 Fin15AnchoredAtom4734 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 12}, {0, 8, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 6, 8, 10, 12}, {0, 6, 8, 9, 12}, {0, 6, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29290 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom4735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2717 Fin15AnchoredAtom2720 Fin15AnchoredAtom2724
    Fin15AnchoredAtom2734 Fin15AnchoredAtom2789 Fin15AnchoredAtom4735 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 13}, {0, 8, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29291 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2719 Fin15AnchoredAtom2720 Fin15AnchoredAtom2729
    Fin15AnchoredAtom2739 Fin15AnchoredAtom2794 Fin15AnchoredAtom4740 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 12, 13}, {0, 8, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 9, 13}, {0, 6, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29292 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2719 Fin15AnchoredAtom2721 Fin15AnchoredAtom2730
    Fin15AnchoredAtom2740 Fin15AnchoredAtom2795 Fin15AnchoredAtom4741 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 8, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 12, 14}, {0, 8, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29293 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2720 Fin15AnchoredAtom2721 Fin15AnchoredAtom2731
    Fin15AnchoredAtom2741 Fin15AnchoredAtom2796 Fin15AnchoredAtom4742 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 13, 14}, {0, 8, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 8, 9, 14}, {0, 6, 8, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29294 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom4746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2723 Fin15AnchoredAtom2724 Fin15AnchoredAtom2729
    Fin15AnchoredAtom2745 Fin15AnchoredAtom2800 Fin15AnchoredAtom4746 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 8, 12, 13}, {0, 6, 8, 10, 13}, {0, 6, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29295 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2723 Fin15AnchoredAtom2725 Fin15AnchoredAtom2730
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2801 Fin15AnchoredAtom4747 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29296 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2724 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom4748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2724 Fin15AnchoredAtom2725 Fin15AnchoredAtom2731
    Fin15AnchoredAtom2747 Fin15AnchoredAtom2802 Fin15AnchoredAtom4748 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 8, 10, 14}, {0, 6, 8, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29297 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2729 Fin15AnchoredAtom2730 Fin15AnchoredAtom2731
    Fin15AnchoredAtom2751 Fin15AnchoredAtom2806 Fin15AnchoredAtom4752 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 8, 13, 14}, {0, 6, 8, 12, 14}, {0, 6, 8, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29298 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2732 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2736 chi ∧
      Fin15AnchoredAtom2742 chi ∧
      Fin15AnchoredAtom2807 chi ∧
      Fin15AnchoredAtom4753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2732 Fin15AnchoredAtom2733 Fin15AnchoredAtom2736
    Fin15AnchoredAtom2742 Fin15AnchoredAtom2807 Fin15AnchoredAtom4753 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 9, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 11, 12}, {0, 9, 10, 11, 12}, {0, 6, 10, 11, 12}, {0, 6, 9, 11, 12}, {0, 6, 9, 10, 12}, {0, 6, 9, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29299 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2733 Fin15AnchoredAtom2734 Fin15AnchoredAtom2739
    Fin15AnchoredAtom2745 Fin15AnchoredAtom2810 Fin15AnchoredAtom4756 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {0, 9, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 6, 9, 12, 13}, {0, 6, 9, 10, 13}, {0, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29300 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2733 Fin15AnchoredAtom2735 Fin15AnchoredAtom2740
    Fin15AnchoredAtom2746 Fin15AnchoredAtom2811 Fin15AnchoredAtom4757 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {0, 9, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29301 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2734 Fin15AnchoredAtom2735 Fin15AnchoredAtom2741
    Fin15AnchoredAtom2747 Fin15AnchoredAtom2812 Fin15AnchoredAtom4758 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {0, 9, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 10, 14}, {0, 6, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29302 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2739 Fin15AnchoredAtom2740 Fin15AnchoredAtom2741
    Fin15AnchoredAtom2751 Fin15AnchoredAtom2816 Fin15AnchoredAtom4762 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 9, 13, 14}, {0, 6, 9, 12, 14}, {0, 6, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29303 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2745 Fin15AnchoredAtom2746 Fin15AnchoredAtom2747
    Fin15AnchoredAtom2751 Fin15AnchoredAtom2820 Fin15AnchoredAtom4766 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 6, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 6, 10, 13, 14}, {0, 6, 10, 12, 14}, {0, 6, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29304 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2752 Fin15AnchoredAtom2754 Fin15AnchoredAtom2758
    Fin15AnchoredAtom2768 Fin15AnchoredAtom2788 Fin15AnchoredAtom4769 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 12}, {0, 8, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 7, 8, 10, 12}, {0, 7, 8, 9, 12}, {0, 7, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29305 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom4770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2752 Fin15AnchoredAtom2755 Fin15AnchoredAtom2759
    Fin15AnchoredAtom2769 Fin15AnchoredAtom2789 Fin15AnchoredAtom4770 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 13}, {0, 8, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29306 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom2790 chi ∧
      Fin15AnchoredAtom4771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2752 Fin15AnchoredAtom2756 Fin15AnchoredAtom2760
    Fin15AnchoredAtom2770 Fin15AnchoredAtom2790 Fin15AnchoredAtom4771 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 14}, {0, 8, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29307 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2754 Fin15AnchoredAtom2755 Fin15AnchoredAtom2764
    Fin15AnchoredAtom2774 Fin15AnchoredAtom2794 Fin15AnchoredAtom4775 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 13}, {0, 8, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 7, 8, 12, 13}, {0, 7, 8, 9, 13}, {0, 7, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29308 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2754 Fin15AnchoredAtom2756 Fin15AnchoredAtom2765
    Fin15AnchoredAtom2775 Fin15AnchoredAtom2795 Fin15AnchoredAtom4776 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 12, 14}, {0, 8, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29309 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2755 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2755 Fin15AnchoredAtom2756 Fin15AnchoredAtom2766
    Fin15AnchoredAtom2776 Fin15AnchoredAtom2796 Fin15AnchoredAtom4777 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 13, 14}, {0, 8, 9, 13, 14}, {0, 7, 9, 13, 14}, {0, 7, 8, 13, 14}, {0, 7, 8, 9, 14}, {0, 7, 8, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29310 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom4781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2758 Fin15AnchoredAtom2759 Fin15AnchoredAtom2764
    Fin15AnchoredAtom2780 Fin15AnchoredAtom2800 Fin15AnchoredAtom4781 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 7, 8, 12, 13}, {0, 7, 8, 10, 13}, {0, 7, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause29311 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2758 Fin15AnchoredAtom2760 Fin15AnchoredAtom2765
    Fin15AnchoredAtom2781 Fin15AnchoredAtom2801 Fin15AnchoredAtom4782 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 7, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 7, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 7, 8, 12, 14}, {0, 7, 8, 10, 14}, {0, 7, 8, 10, 12}] : List (Finset (Fin 15))) :
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

end ErdosSzekeres

end
