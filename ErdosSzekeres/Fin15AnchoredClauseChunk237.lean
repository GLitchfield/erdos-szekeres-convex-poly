module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 237. -/

theorem fin15Anchored_clause30336 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4369 chi ∧
      Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom4467 chi ∧
      Fin15AnchoredAtom4593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4369 Fin15AnchoredAtom4370 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4411 Fin15AnchoredAtom4467 Fin15AnchoredAtom4593 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 10}, {4, 6, 8, 9, 10}, {4, 5, 8, 9, 10}, {4, 5, 6, 9, 10}, {4, 5, 6, 8, 10}, {4, 5, 6, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30337 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4369 chi ∧
      Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4470 chi ∧
      Fin15AnchoredAtom4596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4369 Fin15AnchoredAtom4373 Fin15AnchoredAtom4378
    Fin15AnchoredAtom4414 Fin15AnchoredAtom4470 Fin15AnchoredAtom4596 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 13}, {4, 6, 8, 9, 13}, {4, 5, 8, 9, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30338 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4372 chi ∧
      Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom4599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4370 Fin15AnchoredAtom4372 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4417 Fin15AnchoredAtom4473 Fin15AnchoredAtom4599 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 12}, {4, 6, 8, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 8, 12}, {4, 5, 6, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30339 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4474 chi ∧
      Fin15AnchoredAtom4600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4370 Fin15AnchoredAtom4373 Fin15AnchoredAtom4382
    Fin15AnchoredAtom4418 Fin15AnchoredAtom4474 Fin15AnchoredAtom4600 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 13}, {4, 6, 8, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30340 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4374 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4419 chi ∧
      Fin15AnchoredAtom4475 chi ∧
      Fin15AnchoredAtom4601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4370 Fin15AnchoredAtom4374 Fin15AnchoredAtom4383
    Fin15AnchoredAtom4419 Fin15AnchoredAtom4475 Fin15AnchoredAtom4601 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 14}, {4, 6, 8, 10, 14}, {4, 5, 8, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30341 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4372 chi ∧
      Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom4605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4372 Fin15AnchoredAtom4373 Fin15AnchoredAtom4387
    Fin15AnchoredAtom4423 Fin15AnchoredAtom4479 Fin15AnchoredAtom4605 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 12, 13}, {4, 6, 8, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 8, 13}, {4, 5, 6, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30342 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom4374 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4481 chi ∧
      Fin15AnchoredAtom4607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4373 Fin15AnchoredAtom4374 Fin15AnchoredAtom4389
    Fin15AnchoredAtom4425 Fin15AnchoredAtom4481 Fin15AnchoredAtom4607 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 13, 14}, {4, 6, 8, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 8, 14}, {4, 5, 6, 8, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30343 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4375 Fin15AnchoredAtom4377 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4427 Fin15AnchoredAtom4483 Fin15AnchoredAtom4609 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30344 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom4610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4375 Fin15AnchoredAtom4378 Fin15AnchoredAtom4382
    Fin15AnchoredAtom4428 Fin15AnchoredAtom4484 Fin15AnchoredAtom4610 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30345 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom4611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4375 Fin15AnchoredAtom4379 Fin15AnchoredAtom4383
    Fin15AnchoredAtom4429 Fin15AnchoredAtom4485 Fin15AnchoredAtom4611 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30346 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4377 Fin15AnchoredAtom4378 Fin15AnchoredAtom4387
    Fin15AnchoredAtom4433 Fin15AnchoredAtom4489 Fin15AnchoredAtom4615 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30347 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom4616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4377 Fin15AnchoredAtom4379 Fin15AnchoredAtom4388
    Fin15AnchoredAtom4434 Fin15AnchoredAtom4490 Fin15AnchoredAtom4616 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30348 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom4617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4378 Fin15AnchoredAtom4379 Fin15AnchoredAtom4389
    Fin15AnchoredAtom4435 Fin15AnchoredAtom4491 Fin15AnchoredAtom4617 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30349 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4381 Fin15AnchoredAtom4382 Fin15AnchoredAtom4387
    Fin15AnchoredAtom4439 Fin15AnchoredAtom4495 Fin15AnchoredAtom4621 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30350 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4381 Fin15AnchoredAtom4383 Fin15AnchoredAtom4388
    Fin15AnchoredAtom4440 Fin15AnchoredAtom4496 Fin15AnchoredAtom4622 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30351 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4382 Fin15AnchoredAtom4383 Fin15AnchoredAtom4389
    Fin15AnchoredAtom4441 Fin15AnchoredAtom4497 Fin15AnchoredAtom4623 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30352 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4387 Fin15AnchoredAtom4388 Fin15AnchoredAtom4389
    Fin15AnchoredAtom4445 Fin15AnchoredAtom4501 Fin15AnchoredAtom4627 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30353 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom4502 chi ∧
      Fin15AnchoredAtom4628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4390 Fin15AnchoredAtom4391 Fin15AnchoredAtom4396
    Fin15AnchoredAtom4411 Fin15AnchoredAtom4502 Fin15AnchoredAtom4628 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 10}, {4, 7, 8, 9, 10}, {4, 5, 8, 9, 10}, {4, 5, 7, 9, 10}, {4, 5, 7, 8, 10}, {4, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30354 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4413 chi ∧
      Fin15AnchoredAtom4504 chi ∧
      Fin15AnchoredAtom4630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4390 Fin15AnchoredAtom4393 Fin15AnchoredAtom4398
    Fin15AnchoredAtom4413 Fin15AnchoredAtom4504 Fin15AnchoredAtom4630 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 12}, {4, 7, 8, 9, 12}, {4, 5, 8, 9, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30355 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4505 chi ∧
      Fin15AnchoredAtom4631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4390 Fin15AnchoredAtom4394 Fin15AnchoredAtom4399
    Fin15AnchoredAtom4414 Fin15AnchoredAtom4505 Fin15AnchoredAtom4631 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 13}, {4, 7, 8, 9, 13}, {4, 5, 8, 9, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30356 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom4508 chi ∧
      Fin15AnchoredAtom4634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4391 Fin15AnchoredAtom4393 Fin15AnchoredAtom4402
    Fin15AnchoredAtom4417 Fin15AnchoredAtom4508 Fin15AnchoredAtom4634 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 12}, {4, 7, 8, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 8, 12}, {4, 5, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30357 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4509 chi ∧
      Fin15AnchoredAtom4635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4391 Fin15AnchoredAtom4394 Fin15AnchoredAtom4403
    Fin15AnchoredAtom4418 Fin15AnchoredAtom4509 Fin15AnchoredAtom4635 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 13}, {4, 7, 8, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30358 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4514 chi ∧
      Fin15AnchoredAtom4640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4393 Fin15AnchoredAtom4394 Fin15AnchoredAtom4408
    Fin15AnchoredAtom4423 Fin15AnchoredAtom4514 Fin15AnchoredAtom4640 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 12, 13}, {4, 7, 8, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 8, 13}, {4, 5, 7, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30359 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom4395 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4424 chi ∧
      Fin15AnchoredAtom4515 chi ∧
      Fin15AnchoredAtom4641 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4393 Fin15AnchoredAtom4395 Fin15AnchoredAtom4409
    Fin15AnchoredAtom4424 Fin15AnchoredAtom4515 Fin15AnchoredAtom4641 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 12, 14}, {4, 7, 8, 12, 14}, {4, 5, 8, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30360 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom4395 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4516 chi ∧
      Fin15AnchoredAtom4642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4394 Fin15AnchoredAtom4395 Fin15AnchoredAtom4410
    Fin15AnchoredAtom4425 Fin15AnchoredAtom4516 Fin15AnchoredAtom4642 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 13, 14}, {4, 7, 8, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 8, 14}, {4, 5, 7, 8, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30361 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4397 chi ∧
      Fin15AnchoredAtom4401 chi ∧
      Fin15AnchoredAtom4426 chi ∧
      Fin15AnchoredAtom4517 chi ∧
      Fin15AnchoredAtom4643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4396 Fin15AnchoredAtom4397 Fin15AnchoredAtom4401
    Fin15AnchoredAtom4426 Fin15AnchoredAtom4517 Fin15AnchoredAtom4643 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 9, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 11}, {4, 7, 9, 10, 11}, {4, 5, 9, 10, 11}, {4, 5, 7, 10, 11}, {4, 5, 7, 9, 11}, {4, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30362 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom4644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4396 Fin15AnchoredAtom4398 Fin15AnchoredAtom4402
    Fin15AnchoredAtom4427 Fin15AnchoredAtom4518 Fin15AnchoredAtom4644 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 7, 9, 12}, {4, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30363 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom4645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4396 Fin15AnchoredAtom4399 Fin15AnchoredAtom4403
    Fin15AnchoredAtom4428 Fin15AnchoredAtom4519 Fin15AnchoredAtom4645 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30364 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom4646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4396 Fin15AnchoredAtom4400 Fin15AnchoredAtom4404
    Fin15AnchoredAtom4429 Fin15AnchoredAtom4520 Fin15AnchoredAtom4646 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 5, 9, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30365 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom4650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4398 Fin15AnchoredAtom4399 Fin15AnchoredAtom4408
    Fin15AnchoredAtom4433 Fin15AnchoredAtom4524 Fin15AnchoredAtom4650 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 9, 13}, {4, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30366 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom4651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4398 Fin15AnchoredAtom4400 Fin15AnchoredAtom4409
    Fin15AnchoredAtom4434 Fin15AnchoredAtom4525 Fin15AnchoredAtom4651 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30367 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4399 Fin15AnchoredAtom4400 Fin15AnchoredAtom4410
    Fin15AnchoredAtom4435 Fin15AnchoredAtom4526 Fin15AnchoredAtom4652 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 9, 14}, {4, 5, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30368 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4402 Fin15AnchoredAtom4403 Fin15AnchoredAtom4408
    Fin15AnchoredAtom4439 Fin15AnchoredAtom4530 Fin15AnchoredAtom4656 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 7, 10, 13}, {4, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30369 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4402 Fin15AnchoredAtom4404 Fin15AnchoredAtom4409
    Fin15AnchoredAtom4440 Fin15AnchoredAtom4531 Fin15AnchoredAtom4657 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30370 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4403 Fin15AnchoredAtom4404 Fin15AnchoredAtom4410
    Fin15AnchoredAtom4441 Fin15AnchoredAtom4532 Fin15AnchoredAtom4658 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 10, 14}, {4, 5, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30371 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom4662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4408 Fin15AnchoredAtom4409 Fin15AnchoredAtom4410
    Fin15AnchoredAtom4445 Fin15AnchoredAtom4536 Fin15AnchoredAtom4662 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 7, 12, 14}, {4, 5, 7, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30372 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom4413 chi ∧
      Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom4664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4411 Fin15AnchoredAtom4413 Fin15AnchoredAtom4417
    Fin15AnchoredAtom4427 Fin15AnchoredAtom4538 Fin15AnchoredAtom4664 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 12}, {4, 8, 9, 10, 12}, {4, 5, 9, 10, 12}, {4, 5, 8, 10, 12}, {4, 5, 8, 9, 12}, {4, 5, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30373 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4539 chi ∧
      Fin15AnchoredAtom4665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4411 Fin15AnchoredAtom4414 Fin15AnchoredAtom4418
    Fin15AnchoredAtom4428 Fin15AnchoredAtom4539 Fin15AnchoredAtom4665 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 13}, {4, 8, 9, 10, 13}, {4, 5, 9, 10, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30374 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4413 chi ∧
      Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4544 chi ∧
      Fin15AnchoredAtom4670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4413 Fin15AnchoredAtom4414 Fin15AnchoredAtom4423
    Fin15AnchoredAtom4433 Fin15AnchoredAtom4544 Fin15AnchoredAtom4670 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 12, 13}, {4, 8, 9, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 8, 9, 13}, {4, 5, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30375 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4414 chi ∧
      Fin15AnchoredAtom4415 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4546 chi ∧
      Fin15AnchoredAtom4672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4414 Fin15AnchoredAtom4415 Fin15AnchoredAtom4425
    Fin15AnchoredAtom4435 Fin15AnchoredAtom4546 Fin15AnchoredAtom4672 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 13, 14}, {4, 8, 9, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 8, 9, 14}, {4, 5, 8, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30376 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4417 chi ∧
      Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4417 Fin15AnchoredAtom4418 Fin15AnchoredAtom4423
    Fin15AnchoredAtom4439 Fin15AnchoredAtom4550 Fin15AnchoredAtom4676 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 8, 12, 13}, {4, 5, 8, 10, 13}, {4, 5, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30377 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4418 chi ∧
      Fin15AnchoredAtom4419 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom4678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4418 Fin15AnchoredAtom4419 Fin15AnchoredAtom4425
    Fin15AnchoredAtom4441 Fin15AnchoredAtom4552 Fin15AnchoredAtom4678 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 13, 14}, {4, 8, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 8, 10, 14}, {4, 5, 8, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30378 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4423 chi ∧
      Fin15AnchoredAtom4424 chi ∧
      Fin15AnchoredAtom4425 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4556 chi ∧
      Fin15AnchoredAtom4682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4423 Fin15AnchoredAtom4424 Fin15AnchoredAtom4425
    Fin15AnchoredAtom4445 Fin15AnchoredAtom4556 Fin15AnchoredAtom4682 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 12, 13, 14}, {4, 8, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 8, 13, 14}, {4, 5, 8, 12, 14}, {4, 5, 8, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30379 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4427 Fin15AnchoredAtom4428 Fin15AnchoredAtom4433
    Fin15AnchoredAtom4439 Fin15AnchoredAtom4560 Fin15AnchoredAtom4686 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 9, 12, 13}, {4, 5, 9, 10, 13}, {4, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30380 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4427 chi ∧
      Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4427 Fin15AnchoredAtom4429 Fin15AnchoredAtom4434
    Fin15AnchoredAtom4440 Fin15AnchoredAtom4561 Fin15AnchoredAtom4687 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 5, 10, 12, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30381 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4428 chi ∧
      Fin15AnchoredAtom4429 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom4688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4428 Fin15AnchoredAtom4429 Fin15AnchoredAtom4435
    Fin15AnchoredAtom4441 Fin15AnchoredAtom4562 Fin15AnchoredAtom4688 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 10, 14}, {4, 5, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30382 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4433 chi ∧
      Fin15AnchoredAtom4434 chi ∧
      Fin15AnchoredAtom4435 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom4692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4433 Fin15AnchoredAtom4434 Fin15AnchoredAtom4435
    Fin15AnchoredAtom4445 Fin15AnchoredAtom4566 Fin15AnchoredAtom4692 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 9, 13, 14}, {4, 5, 9, 12, 14}, {4, 5, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30383 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4436 chi ∧
      Fin15AnchoredAtom4437 chi ∧
      Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4442 chi ∧
      Fin15AnchoredAtom4567 chi ∧
      Fin15AnchoredAtom4693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4436 Fin15AnchoredAtom4437 Fin15AnchoredAtom4439
    Fin15AnchoredAtom4442 Fin15AnchoredAtom4567 Fin15AnchoredAtom4693 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 10, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 11, 12, 13}, {4, 10, 11, 12, 13}, {4, 5, 11, 12, 13}, {4, 5, 10, 12, 13}, {4, 5, 10, 11, 13}, {4, 5, 10, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30384 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4439 chi ∧
      Fin15AnchoredAtom4440 chi ∧
      Fin15AnchoredAtom4441 chi ∧
      Fin15AnchoredAtom4445 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4439 Fin15AnchoredAtom4440 Fin15AnchoredAtom4441
    Fin15AnchoredAtom4445 Fin15AnchoredAtom4570 Fin15AnchoredAtom4696 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 5, 12, 13, 14}, {4, 5, 10, 13, 14}, {4, 5, 10, 12, 14}, {4, 5, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30385 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4446 chi ∧
      Fin15AnchoredAtom4447 chi ∧
      Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4467 chi ∧
      Fin15AnchoredAtom4502 chi ∧
      Fin15AnchoredAtom4698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4446 Fin15AnchoredAtom4447 Fin15AnchoredAtom4452
    Fin15AnchoredAtom4467 Fin15AnchoredAtom4502 Fin15AnchoredAtom4698 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 10}, {4, 7, 8, 9, 10}, {4, 6, 8, 9, 10}, {4, 6, 7, 9, 10}, {4, 6, 7, 8, 10}, {4, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30386 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4449 chi ∧
      Fin15AnchoredAtom4451 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4480 chi ∧
      Fin15AnchoredAtom4515 chi ∧
      Fin15AnchoredAtom4711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4449 Fin15AnchoredAtom4451 Fin15AnchoredAtom4465
    Fin15AnchoredAtom4480 Fin15AnchoredAtom4515 Fin15AnchoredAtom4711 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 12, 14}, {4, 7, 8, 12, 14}, {4, 6, 8, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 8, 14}, {4, 6, 7, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30387 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom4714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4452 Fin15AnchoredAtom4454 Fin15AnchoredAtom4458
    Fin15AnchoredAtom4483 Fin15AnchoredAtom4518 Fin15AnchoredAtom4714 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {4, 7, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 7, 10, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30388 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom4715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4452 Fin15AnchoredAtom4455 Fin15AnchoredAtom4459
    Fin15AnchoredAtom4484 Fin15AnchoredAtom4519 Fin15AnchoredAtom4715 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {4, 7, 9, 10, 13}, {4, 6, 9, 10, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30389 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom4716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4452 Fin15AnchoredAtom4456 Fin15AnchoredAtom4460
    Fin15AnchoredAtom4485 Fin15AnchoredAtom4520 Fin15AnchoredAtom4716 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {4, 7, 9, 10, 14}, {4, 6, 9, 10, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30390 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4453 chi ∧
      Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4461 chi ∧
      Fin15AnchoredAtom4486 chi ∧
      Fin15AnchoredAtom4521 chi ∧
      Fin15AnchoredAtom4717 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4453 Fin15AnchoredAtom4454 Fin15AnchoredAtom4461
    Fin15AnchoredAtom4486 Fin15AnchoredAtom4521 Fin15AnchoredAtom4717 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 11, 12}, {4, 7, 9, 11, 12}, {4, 6, 9, 11, 12}, {4, 6, 7, 11, 12}, {4, 6, 7, 9, 12}, {4, 6, 7, 9, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30391 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom4720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4454 Fin15AnchoredAtom4455 Fin15AnchoredAtom4464
    Fin15AnchoredAtom4489 Fin15AnchoredAtom4524 Fin15AnchoredAtom4720 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {4, 7, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 9, 13}, {4, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30392 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom4721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4454 Fin15AnchoredAtom4456 Fin15AnchoredAtom4465
    Fin15AnchoredAtom4490 Fin15AnchoredAtom4525 Fin15AnchoredAtom4721 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {4, 7, 9, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30393 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4455 Fin15AnchoredAtom4456 Fin15AnchoredAtom4466
    Fin15AnchoredAtom4491 Fin15AnchoredAtom4526 Fin15AnchoredAtom4722 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 9, 14}, {4, 6, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30394 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4458 Fin15AnchoredAtom4459 Fin15AnchoredAtom4464
    Fin15AnchoredAtom4495 Fin15AnchoredAtom4530 Fin15AnchoredAtom4726 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 7, 12, 13}, {4, 6, 7, 10, 13}, {4, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30395 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4458 Fin15AnchoredAtom4460 Fin15AnchoredAtom4465
    Fin15AnchoredAtom4496 Fin15AnchoredAtom4531 Fin15AnchoredAtom4727 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30396 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4459 Fin15AnchoredAtom4460 Fin15AnchoredAtom4466
    Fin15AnchoredAtom4497 Fin15AnchoredAtom4532 Fin15AnchoredAtom4728 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 10, 14}, {4, 6, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30397 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom4732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4464 Fin15AnchoredAtom4465 Fin15AnchoredAtom4466
    Fin15AnchoredAtom4501 Fin15AnchoredAtom4536 Fin15AnchoredAtom4732 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 7, 13, 14}, {4, 6, 7, 12, 14}, {4, 6, 7, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30398 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4467 chi ∧
      Fin15AnchoredAtom4469 chi ∧
      Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom4734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4467 Fin15AnchoredAtom4469 Fin15AnchoredAtom4473
    Fin15AnchoredAtom4483 Fin15AnchoredAtom4538 Fin15AnchoredAtom4734 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 12}, {4, 8, 9, 10, 12}, {4, 6, 9, 10, 12}, {4, 6, 8, 10, 12}, {4, 6, 8, 9, 12}, {4, 6, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30399 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4469 chi ∧
      Fin15AnchoredAtom4470 chi ∧
      Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4544 chi ∧
      Fin15AnchoredAtom4740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4469 Fin15AnchoredAtom4470 Fin15AnchoredAtom4479
    Fin15AnchoredAtom4489 Fin15AnchoredAtom4544 Fin15AnchoredAtom4740 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 12, 13}, {4, 8, 9, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 8, 12, 13}, {4, 6, 8, 9, 13}, {4, 6, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30400 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom4474 chi ∧
      Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4473 Fin15AnchoredAtom4474 Fin15AnchoredAtom4479
    Fin15AnchoredAtom4495 Fin15AnchoredAtom4550 Fin15AnchoredAtom4746 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 8, 12, 13}, {4, 6, 8, 10, 13}, {4, 6, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30401 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom4475 chi ∧
      Fin15AnchoredAtom4480 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4551 chi ∧
      Fin15AnchoredAtom4747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4473 Fin15AnchoredAtom4475 Fin15AnchoredAtom4480
    Fin15AnchoredAtom4496 Fin15AnchoredAtom4551 Fin15AnchoredAtom4747 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 14}, {4, 8, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 8, 12, 14}, {4, 6, 8, 10, 14}, {4, 6, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30402 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4474 chi ∧
      Fin15AnchoredAtom4475 chi ∧
      Fin15AnchoredAtom4481 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom4748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4474 Fin15AnchoredAtom4475 Fin15AnchoredAtom4481
    Fin15AnchoredAtom4497 Fin15AnchoredAtom4552 Fin15AnchoredAtom4748 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 13, 14}, {4, 8, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 8, 13, 14}, {4, 6, 8, 10, 14}, {4, 6, 8, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30403 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom4480 chi ∧
      Fin15AnchoredAtom4481 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4556 chi ∧
      Fin15AnchoredAtom4752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4479 Fin15AnchoredAtom4480 Fin15AnchoredAtom4481
    Fin15AnchoredAtom4501 Fin15AnchoredAtom4556 Fin15AnchoredAtom4752 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 12, 13, 14}, {4, 8, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 8, 13, 14}, {4, 6, 8, 12, 14}, {4, 6, 8, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30404 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4483 Fin15AnchoredAtom4484 Fin15AnchoredAtom4489
    Fin15AnchoredAtom4495 Fin15AnchoredAtom4560 Fin15AnchoredAtom4756 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 6, 10, 12, 13}, {4, 6, 9, 12, 13}, {4, 6, 9, 10, 13}, {4, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30405 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4483 Fin15AnchoredAtom4485 Fin15AnchoredAtom4490
    Fin15AnchoredAtom4496 Fin15AnchoredAtom4561 Fin15AnchoredAtom4757 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 6, 10, 12, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30406 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom4758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4484 Fin15AnchoredAtom4485 Fin15AnchoredAtom4491
    Fin15AnchoredAtom4497 Fin15AnchoredAtom4562 Fin15AnchoredAtom4758 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 10, 14}, {4, 6, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30407 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom4762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4489 Fin15AnchoredAtom4490 Fin15AnchoredAtom4491
    Fin15AnchoredAtom4501 Fin15AnchoredAtom4566 Fin15AnchoredAtom4762 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 9, 13, 14}, {4, 6, 9, 12, 14}, {4, 6, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30408 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4495 Fin15AnchoredAtom4496 Fin15AnchoredAtom4497
    Fin15AnchoredAtom4501 Fin15AnchoredAtom4570 Fin15AnchoredAtom4766 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 6, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 6, 12, 13, 14}, {4, 6, 10, 13, 14}, {4, 6, 10, 12, 14}, {4, 6, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30409 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4505 chi ∧
      Fin15AnchoredAtom4506 chi ∧
      Fin15AnchoredAtom4516 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4546 chi ∧
      Fin15AnchoredAtom4777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4505 Fin15AnchoredAtom4506 Fin15AnchoredAtom4516
    Fin15AnchoredAtom4526 Fin15AnchoredAtom4546 Fin15AnchoredAtom4777 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 13, 14}, {4, 8, 9, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 8, 13, 14}, {4, 7, 8, 9, 14}, {4, 7, 8, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30410 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4508 chi ∧
      Fin15AnchoredAtom4509 chi ∧
      Fin15AnchoredAtom4514 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4508 Fin15AnchoredAtom4509 Fin15AnchoredAtom4514
    Fin15AnchoredAtom4530 Fin15AnchoredAtom4550 Fin15AnchoredAtom4781 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 7, 8, 12, 13}, {4, 7, 8, 10, 13}, {4, 7, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30411 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4509 chi ∧
      Fin15AnchoredAtom4510 chi ∧
      Fin15AnchoredAtom4516 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom4783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4509 Fin15AnchoredAtom4510 Fin15AnchoredAtom4516
    Fin15AnchoredAtom4532 Fin15AnchoredAtom4552 Fin15AnchoredAtom4783 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 10, 13, 14}, {4, 8, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 8, 13, 14}, {4, 7, 8, 10, 14}, {4, 7, 8, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30412 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4518 Fin15AnchoredAtom4519 Fin15AnchoredAtom4524
    Fin15AnchoredAtom4530 Fin15AnchoredAtom4560 Fin15AnchoredAtom4791 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 7, 10, 12, 13}, {4, 7, 9, 12, 13}, {4, 7, 9, 10, 13}, {4, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30413 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4518 Fin15AnchoredAtom4520 Fin15AnchoredAtom4525
    Fin15AnchoredAtom4531 Fin15AnchoredAtom4561 Fin15AnchoredAtom4792 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 7, 10, 12, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 10, 14}, {4, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30414 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom4793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4519 Fin15AnchoredAtom4520 Fin15AnchoredAtom4526
    Fin15AnchoredAtom4532 Fin15AnchoredAtom4562 Fin15AnchoredAtom4793 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {4, 9, 10, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 9, 10, 14}, {4, 7, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30415 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom4797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4524 Fin15AnchoredAtom4525 Fin15AnchoredAtom4526
    Fin15AnchoredAtom4536 Fin15AnchoredAtom4566 Fin15AnchoredAtom4797 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 7, 9, 13, 14}, {4, 7, 9, 12, 14}, {4, 7, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30416 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4527 chi ∧
      Fin15AnchoredAtom4528 chi ∧
      Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4533 chi ∧
      Fin15AnchoredAtom4567 chi ∧
      Fin15AnchoredAtom4798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4527 Fin15AnchoredAtom4528 Fin15AnchoredAtom4530
    Fin15AnchoredAtom4533 Fin15AnchoredAtom4567 Fin15AnchoredAtom4798 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 10, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 11, 12, 13}, {4, 10, 11, 12, 13}, {4, 7, 11, 12, 13}, {4, 7, 10, 12, 13}, {4, 7, 10, 11, 13}, {4, 7, 10, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30417 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4527 chi ∧
      Fin15AnchoredAtom4529 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4534 chi ∧
      Fin15AnchoredAtom4568 chi ∧
      Fin15AnchoredAtom4799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4527 Fin15AnchoredAtom4529 Fin15AnchoredAtom4531
    Fin15AnchoredAtom4534 Fin15AnchoredAtom4568 Fin15AnchoredAtom4799 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 10, 11, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 10, 11, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 11, 12, 14}, {4, 10, 11, 12, 14}, {4, 7, 11, 12, 14}, {4, 7, 10, 12, 14}, {4, 7, 10, 11, 14}, {4, 7, 10, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30418 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4530 chi ∧
      Fin15AnchoredAtom4531 chi ∧
      Fin15AnchoredAtom4532 chi ∧
      Fin15AnchoredAtom4536 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4530 Fin15AnchoredAtom4531 Fin15AnchoredAtom4532
    Fin15AnchoredAtom4536 Fin15AnchoredAtom4570 Fin15AnchoredAtom4801 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 7, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 7, 12, 13, 14}, {4, 7, 10, 13, 14}, {4, 7, 10, 12, 14}, {4, 7, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30419 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom4539 chi ∧
      Fin15AnchoredAtom4544 chi ∧
      Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4538 Fin15AnchoredAtom4539 Fin15AnchoredAtom4544
    Fin15AnchoredAtom4550 Fin15AnchoredAtom4560 Fin15AnchoredAtom4806 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 8, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {4, 9, 10, 12, 13}, {4, 8, 10, 12, 13}, {4, 8, 9, 12, 13}, {4, 8, 9, 10, 13}, {4, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30420 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4538 chi ∧
      Fin15AnchoredAtom4540 chi ∧
      Fin15AnchoredAtom4545 chi ∧
      Fin15AnchoredAtom4551 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4538 Fin15AnchoredAtom4540 Fin15AnchoredAtom4545
    Fin15AnchoredAtom4551 Fin15AnchoredAtom4561 Fin15AnchoredAtom4807 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 8, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 8, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 14}, {4, 9, 10, 12, 14}, {4, 8, 10, 12, 14}, {4, 8, 9, 12, 14}, {4, 8, 9, 10, 14}, {4, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30421 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4550 chi ∧
      Fin15AnchoredAtom4551 chi ∧
      Fin15AnchoredAtom4552 chi ∧
      Fin15AnchoredAtom4556 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4550 Fin15AnchoredAtom4551 Fin15AnchoredAtom4552
    Fin15AnchoredAtom4556 Fin15AnchoredAtom4570 Fin15AnchoredAtom4816 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 8, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 8, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 8, 12, 13, 14}, {4, 8, 10, 13, 14}, {4, 8, 10, 12, 14}, {4, 8, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30422 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4560 chi ∧
      Fin15AnchoredAtom4561 chi ∧
      Fin15AnchoredAtom4562 chi ∧
      Fin15AnchoredAtom4566 chi ∧
      Fin15AnchoredAtom4570 chi ∧
      Fin15AnchoredAtom4821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4560 Fin15AnchoredAtom4561 Fin15AnchoredAtom4562
    Fin15AnchoredAtom4566 Fin15AnchoredAtom4570 Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 9, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {4, 10, 12, 13, 14}, {4, 9, 12, 13, 14}, {4, 9, 10, 13, 14}, {4, 9, 10, 12, 14}, {4, 9, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30423 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4572 chi ∧
      Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom4628 chi ∧
      Fin15AnchoredAtom4698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4572 Fin15AnchoredAtom4573 Fin15AnchoredAtom4578
    Fin15AnchoredAtom4593 Fin15AnchoredAtom4628 Fin15AnchoredAtom4698 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 10}, {5, 7, 8, 9, 10}, {5, 6, 8, 9, 10}, {5, 6, 7, 9, 10}, {5, 6, 7, 8, 10}, {5, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30424 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4572 chi ∧
      Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4595 chi ∧
      Fin15AnchoredAtom4630 chi ∧
      Fin15AnchoredAtom4700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4572 Fin15AnchoredAtom4575 Fin15AnchoredAtom4580
    Fin15AnchoredAtom4595 Fin15AnchoredAtom4630 Fin15AnchoredAtom4700 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 12}, {5, 7, 8, 9, 12}, {5, 6, 8, 9, 12}, {5, 6, 7, 9, 12}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30425 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4572 chi ∧
      Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom4631 chi ∧
      Fin15AnchoredAtom4701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4572 Fin15AnchoredAtom4576 Fin15AnchoredAtom4581
    Fin15AnchoredAtom4596 Fin15AnchoredAtom4631 Fin15AnchoredAtom4701 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 9, 13}, {5, 7, 8, 9, 13}, {5, 6, 8, 9, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 9}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30426 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom4634 chi ∧
      Fin15AnchoredAtom4704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4573 Fin15AnchoredAtom4575 Fin15AnchoredAtom4584
    Fin15AnchoredAtom4599 Fin15AnchoredAtom4634 Fin15AnchoredAtom4704 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 12}, {5, 7, 8, 10, 12}, {5, 6, 8, 10, 12}, {5, 6, 7, 10, 12}, {5, 6, 7, 8, 12}, {5, 6, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30427 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom4635 chi ∧
      Fin15AnchoredAtom4705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4573 Fin15AnchoredAtom4576 Fin15AnchoredAtom4585
    Fin15AnchoredAtom4600 Fin15AnchoredAtom4635 Fin15AnchoredAtom4705 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 13}, {5, 7, 8, 10, 13}, {5, 6, 8, 10, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30428 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4573 chi ∧
      Fin15AnchoredAtom4577 chi ∧
      Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom4636 chi ∧
      Fin15AnchoredAtom4706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4573 Fin15AnchoredAtom4577 Fin15AnchoredAtom4586
    Fin15AnchoredAtom4601 Fin15AnchoredAtom4636 Fin15AnchoredAtom4706 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 14}, {5, 7, 8, 10, 14}, {5, 6, 8, 10, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30429 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom4640 chi ∧
      Fin15AnchoredAtom4710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4575 Fin15AnchoredAtom4576 Fin15AnchoredAtom4590
    Fin15AnchoredAtom4605 Fin15AnchoredAtom4640 Fin15AnchoredAtom4710 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 12, 13}, {5, 7, 8, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 8, 13}, {5, 6, 7, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30430 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4575 chi ∧
      Fin15AnchoredAtom4577 chi ∧
      Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom4606 chi ∧
      Fin15AnchoredAtom4641 chi ∧
      Fin15AnchoredAtom4711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4575 Fin15AnchoredAtom4577 Fin15AnchoredAtom4591
    Fin15AnchoredAtom4606 Fin15AnchoredAtom4641 Fin15AnchoredAtom4711 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 12, 14}, {5, 7, 8, 12, 14}, {5, 6, 8, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30431 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4576 chi ∧
      Fin15AnchoredAtom4577 chi ∧
      Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom4642 chi ∧
      Fin15AnchoredAtom4712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4576 Fin15AnchoredAtom4577 Fin15AnchoredAtom4592
    Fin15AnchoredAtom4607 Fin15AnchoredAtom4642 Fin15AnchoredAtom4712 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 13, 14}, {5, 7, 8, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 8, 14}, {5, 6, 7, 8, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30432 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4579 chi ∧
      Fin15AnchoredAtom4583 chi ∧
      Fin15AnchoredAtom4608 chi ∧
      Fin15AnchoredAtom4643 chi ∧
      Fin15AnchoredAtom4713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4578 Fin15AnchoredAtom4579 Fin15AnchoredAtom4583
    Fin15AnchoredAtom4608 Fin15AnchoredAtom4643 Fin15AnchoredAtom4713 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 9, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 11}, {5, 7, 9, 10, 11}, {5, 6, 9, 10, 11}, {5, 6, 7, 10, 11}, {5, 6, 7, 9, 11}, {5, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30433 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4578 Fin15AnchoredAtom4580 Fin15AnchoredAtom4584
    Fin15AnchoredAtom4609 Fin15AnchoredAtom4644 Fin15AnchoredAtom4714 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {5, 7, 9, 10, 12}, {5, 6, 9, 10, 12}, {5, 6, 7, 10, 12}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30434 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom4645 chi ∧
      Fin15AnchoredAtom4715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4578 Fin15AnchoredAtom4581 Fin15AnchoredAtom4585
    Fin15AnchoredAtom4610 Fin15AnchoredAtom4645 Fin15AnchoredAtom4715 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {5, 7, 9, 10, 13}, {5, 6, 9, 10, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30435 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4578 chi ∧
      Fin15AnchoredAtom4582 chi ∧
      Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom4646 chi ∧
      Fin15AnchoredAtom4716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4578 Fin15AnchoredAtom4582 Fin15AnchoredAtom4586
    Fin15AnchoredAtom4611 Fin15AnchoredAtom4646 Fin15AnchoredAtom4716 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {5, 7, 9, 10, 14}, {5, 6, 9, 10, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30436 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4579 chi ∧
      Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4587 chi ∧
      Fin15AnchoredAtom4612 chi ∧
      Fin15AnchoredAtom4647 chi ∧
      Fin15AnchoredAtom4717 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4579 Fin15AnchoredAtom4580 Fin15AnchoredAtom4587
    Fin15AnchoredAtom4612 Fin15AnchoredAtom4647 Fin15AnchoredAtom4717 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 11, 12}, {5, 7, 9, 11, 12}, {5, 6, 9, 11, 12}, {5, 6, 7, 11, 12}, {5, 6, 7, 9, 12}, {5, 6, 7, 9, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30437 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom4650 chi ∧
      Fin15AnchoredAtom4720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4580 Fin15AnchoredAtom4581 Fin15AnchoredAtom4590
    Fin15AnchoredAtom4615 Fin15AnchoredAtom4650 Fin15AnchoredAtom4720 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {5, 7, 9, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 9, 13}, {5, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30438 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4580 chi ∧
      Fin15AnchoredAtom4582 chi ∧
      Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom4616 chi ∧
      Fin15AnchoredAtom4651 chi ∧
      Fin15AnchoredAtom4721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4580 Fin15AnchoredAtom4582 Fin15AnchoredAtom4591
    Fin15AnchoredAtom4616 Fin15AnchoredAtom4651 Fin15AnchoredAtom4721 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {5, 7, 9, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30439 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4581 chi ∧
      Fin15AnchoredAtom4582 chi ∧
      Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom4652 chi ∧
      Fin15AnchoredAtom4722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4581 Fin15AnchoredAtom4582 Fin15AnchoredAtom4592
    Fin15AnchoredAtom4617 Fin15AnchoredAtom4652 Fin15AnchoredAtom4722 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {5, 7, 9, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 9, 14}, {5, 6, 7, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30440 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4656 chi ∧
      Fin15AnchoredAtom4726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4584 Fin15AnchoredAtom4585 Fin15AnchoredAtom4590
    Fin15AnchoredAtom4621 Fin15AnchoredAtom4656 Fin15AnchoredAtom4726 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 7, 12, 13}, {5, 6, 7, 10, 13}, {5, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30441 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4584 chi ∧
      Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom4657 chi ∧
      Fin15AnchoredAtom4727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4584 Fin15AnchoredAtom4586 Fin15AnchoredAtom4591
    Fin15AnchoredAtom4622 Fin15AnchoredAtom4657 Fin15AnchoredAtom4727 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30442 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4585 chi ∧
      Fin15AnchoredAtom4586 chi ∧
      Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom4658 chi ∧
      Fin15AnchoredAtom4728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4585 Fin15AnchoredAtom4586 Fin15AnchoredAtom4592
    Fin15AnchoredAtom4623 Fin15AnchoredAtom4658 Fin15AnchoredAtom4728 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {5, 7, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 10, 14}, {5, 6, 7, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30443 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4590 chi ∧
      Fin15AnchoredAtom4591 chi ∧
      Fin15AnchoredAtom4592 chi ∧
      Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom4732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4590 Fin15AnchoredAtom4591 Fin15AnchoredAtom4592
    Fin15AnchoredAtom4627 Fin15AnchoredAtom4662 Fin15AnchoredAtom4732 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 7, 13, 14}, {5, 6, 7, 12, 14}, {5, 6, 7, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30444 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom4595 chi ∧
      Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom4734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4593 Fin15AnchoredAtom4595 Fin15AnchoredAtom4599
    Fin15AnchoredAtom4609 Fin15AnchoredAtom4664 Fin15AnchoredAtom4734 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 12}, {5, 8, 9, 10, 12}, {5, 6, 9, 10, 12}, {5, 6, 8, 10, 12}, {5, 6, 8, 9, 12}, {5, 6, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30445 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom4665 chi ∧
      Fin15AnchoredAtom4735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4593 Fin15AnchoredAtom4596 Fin15AnchoredAtom4600
    Fin15AnchoredAtom4610 Fin15AnchoredAtom4665 Fin15AnchoredAtom4735 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 13}, {5, 8, 9, 10, 13}, {5, 6, 9, 10, 13}, {5, 6, 8, 10, 13}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30446 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4593 chi ∧
      Fin15AnchoredAtom4597 chi ∧
      Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom4666 chi ∧
      Fin15AnchoredAtom4736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4593 Fin15AnchoredAtom4597 Fin15AnchoredAtom4601
    Fin15AnchoredAtom4611 Fin15AnchoredAtom4666 Fin15AnchoredAtom4736 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 8, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 8, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 10, 14}, {5, 8, 9, 10, 14}, {5, 6, 9, 10, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30447 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4595 chi ∧
      Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom4670 chi ∧
      Fin15AnchoredAtom4740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4595 Fin15AnchoredAtom4596 Fin15AnchoredAtom4605
    Fin15AnchoredAtom4615 Fin15AnchoredAtom4670 Fin15AnchoredAtom4740 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 12, 13}, {5, 8, 9, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 8, 9, 13}, {5, 6, 8, 9, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30448 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom4597 chi ∧
      Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom4672 chi ∧
      Fin15AnchoredAtom4742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4596 Fin15AnchoredAtom4597 Fin15AnchoredAtom4607
    Fin15AnchoredAtom4617 Fin15AnchoredAtom4672 Fin15AnchoredAtom4742 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 13, 14}, {5, 8, 9, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 9, 14}, {5, 6, 8, 9, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30449 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4676 chi ∧
      Fin15AnchoredAtom4746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4599 Fin15AnchoredAtom4600 Fin15AnchoredAtom4605
    Fin15AnchoredAtom4621 Fin15AnchoredAtom4676 Fin15AnchoredAtom4746 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 13}, {5, 8, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 8, 12, 13}, {5, 6, 8, 10, 13}, {5, 6, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30450 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom4606 chi ∧
      Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom4677 chi ∧
      Fin15AnchoredAtom4747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4599 Fin15AnchoredAtom4601 Fin15AnchoredAtom4606
    Fin15AnchoredAtom4622 Fin15AnchoredAtom4677 Fin15AnchoredAtom4747 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 14}, {5, 8, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 8, 12, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30451 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom4678 chi ∧
      Fin15AnchoredAtom4748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4600 Fin15AnchoredAtom4601 Fin15AnchoredAtom4607
    Fin15AnchoredAtom4623 Fin15AnchoredAtom4678 Fin15AnchoredAtom4748 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 13, 14}, {5, 8, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 10, 14}, {5, 6, 8, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30452 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom4606 chi ∧
      Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom4752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4605 Fin15AnchoredAtom4606 Fin15AnchoredAtom4607
    Fin15AnchoredAtom4627 Fin15AnchoredAtom4682 Fin15AnchoredAtom4752 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 12, 13, 14}, {5, 8, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 8, 13, 14}, {5, 6, 8, 12, 14}, {5, 6, 8, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30453 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom4756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4609 Fin15AnchoredAtom4610 Fin15AnchoredAtom4615
    Fin15AnchoredAtom4621 Fin15AnchoredAtom4686 Fin15AnchoredAtom4756 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 9, 12, 13}, {5, 6, 9, 10, 13}, {5, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30454 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom4616 chi ∧
      Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom4757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4609 Fin15AnchoredAtom4611 Fin15AnchoredAtom4616
    Fin15AnchoredAtom4622 Fin15AnchoredAtom4687 Fin15AnchoredAtom4757 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 6, 10, 12, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30455 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom4688 chi ∧
      Fin15AnchoredAtom4758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4610 Fin15AnchoredAtom4611 Fin15AnchoredAtom4617
    Fin15AnchoredAtom4623 Fin15AnchoredAtom4688 Fin15AnchoredAtom4758 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {5, 9, 10, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 10, 14}, {5, 6, 9, 10, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30456 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom4616 chi ∧
      Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom4692 chi ∧
      Fin15AnchoredAtom4762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4615 Fin15AnchoredAtom4616 Fin15AnchoredAtom4617
    Fin15AnchoredAtom4627 Fin15AnchoredAtom4692 Fin15AnchoredAtom4762 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {5, 9, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 9, 13, 14}, {5, 6, 9, 12, 14}, {5, 6, 9, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30457 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4618 chi ∧
      Fin15AnchoredAtom4619 chi ∧
      Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4624 chi ∧
      Fin15AnchoredAtom4693 chi ∧
      Fin15AnchoredAtom4763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4618 Fin15AnchoredAtom4619 Fin15AnchoredAtom4621
    Fin15AnchoredAtom4624 Fin15AnchoredAtom4693 Fin15AnchoredAtom4763 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 10, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 11, 12, 13}, {5, 10, 11, 12, 13}, {5, 6, 11, 12, 13}, {5, 6, 10, 12, 13}, {5, 6, 10, 11, 13}, {5, 6, 10, 11, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30458 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom4627 chi ∧
      Fin15AnchoredAtom4696 chi ∧
      Fin15AnchoredAtom4766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4621 Fin15AnchoredAtom4622 Fin15AnchoredAtom4623
    Fin15AnchoredAtom4627 Fin15AnchoredAtom4696 Fin15AnchoredAtom4766 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 6, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {5, 10, 12, 13, 14}, {5, 6, 12, 13, 14}, {5, 6, 10, 13, 14}, {5, 6, 10, 12, 14}, {5, 6, 10, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30459 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4628 chi ∧
      Fin15AnchoredAtom4630 chi ∧
      Fin15AnchoredAtom4634 chi ∧
      Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4664 chi ∧
      Fin15AnchoredAtom4769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4628 Fin15AnchoredAtom4630 Fin15AnchoredAtom4634
    Fin15AnchoredAtom4644 Fin15AnchoredAtom4664 Fin15AnchoredAtom4769 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 7, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 7, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 10, 12}, {5, 8, 9, 10, 12}, {5, 7, 9, 10, 12}, {5, 7, 8, 10, 12}, {5, 7, 8, 9, 12}, {5, 7, 8, 9, 10}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30460 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4640 chi ∧
      Fin15AnchoredAtom4641 chi ∧
      Fin15AnchoredAtom4642 chi ∧
      Fin15AnchoredAtom4662 chi ∧
      Fin15AnchoredAtom4682 chi ∧
      Fin15AnchoredAtom4787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4640 Fin15AnchoredAtom4641 Fin15AnchoredAtom4642
    Fin15AnchoredAtom4662 Fin15AnchoredAtom4682 Fin15AnchoredAtom4787 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 7, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 7, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 7, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 12, 13, 14}, {5, 8, 12, 13, 14}, {5, 7, 12, 13, 14}, {5, 7, 8, 13, 14}, {5, 7, 8, 12, 14}, {5, 7, 8, 12, 13}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30461 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4643 chi ∧
      Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4647 chi ∧
      Fin15AnchoredAtom4653 chi ∧
      Fin15AnchoredAtom4683 chi ∧
      Fin15AnchoredAtom4788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4643 Fin15AnchoredAtom4644 Fin15AnchoredAtom4647
    Fin15AnchoredAtom4653 Fin15AnchoredAtom4683 Fin15AnchoredAtom4788 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 7, 9, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 7, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 7, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 11, 12}, {5, 9, 10, 11, 12}, {5, 7, 10, 11, 12}, {5, 7, 9, 11, 12}, {5, 7, 9, 10, 12}, {5, 7, 9, 10, 11}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30462 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4645 chi ∧
      Fin15AnchoredAtom4650 chi ∧
      Fin15AnchoredAtom4656 chi ∧
      Fin15AnchoredAtom4686 chi ∧
      Fin15AnchoredAtom4791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4644 Fin15AnchoredAtom4645 Fin15AnchoredAtom4650
    Fin15AnchoredAtom4656 Fin15AnchoredAtom4686 Fin15AnchoredAtom4791 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 7, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {5, 9, 10, 12, 13}, {5, 7, 10, 12, 13}, {5, 7, 9, 12, 13}, {5, 7, 9, 10, 13}, {5, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
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

theorem fin15Anchored_clause30463 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4644 chi ∧
      Fin15AnchoredAtom4646 chi ∧
      Fin15AnchoredAtom4651 chi ∧
      Fin15AnchoredAtom4657 chi ∧
      Fin15AnchoredAtom4687 chi ∧
      Fin15AnchoredAtom4792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4644 Fin15AnchoredAtom4646 Fin15AnchoredAtom4651
    Fin15AnchoredAtom4657 Fin15AnchoredAtom4687 Fin15AnchoredAtom4792 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{5, 7, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({5, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({5, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {5, 9, 10, 12, 14}, {5, 7, 10, 12, 14}, {5, 7, 9, 12, 14}, {5, 7, 9, 10, 14}, {5, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
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
