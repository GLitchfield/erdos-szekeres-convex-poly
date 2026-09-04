module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 233. -/

theorem fin15Anchored_clause29824 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom4592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3332 Fin15AnchoredAtom3333 Fin15AnchoredAtom3354
    Fin15AnchoredAtom3375 Fin15AnchoredAtom3431 Fin15AnchoredAtom4592 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {1, 6, 7, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29825 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3334 chi ∧
      Fin15AnchoredAtom3337 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3378 chi ∧
      Fin15AnchoredAtom3434 chi ∧
      Fin15AnchoredAtom4595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3334 Fin15AnchoredAtom3337 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3378 Fin15AnchoredAtom3434 Fin15AnchoredAtom4595 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 9, 12}, {1, 6, 8, 9, 12}, {1, 5, 8, 9, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 8, 12}, {1, 5, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29826 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3335 chi ∧
      Fin15AnchoredAtom3338 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom3439 chi ∧
      Fin15AnchoredAtom4600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3335 Fin15AnchoredAtom3338 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3383 Fin15AnchoredAtom3439 Fin15AnchoredAtom4600 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 13}, {1, 6, 8, 10, 13}, {1, 5, 8, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 8, 13}, {1, 5, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29827 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3337 chi ∧
      Fin15AnchoredAtom3338 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom4605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3337 Fin15AnchoredAtom3338 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3388 Fin15AnchoredAtom3444 Fin15AnchoredAtom4605 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 12, 13}, {1, 6, 8, 12, 13}, {1, 5, 8, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 8, 13}, {1, 5, 6, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29828 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom4609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3340 Fin15AnchoredAtom3342 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3392 Fin15AnchoredAtom3448 Fin15AnchoredAtom4609 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29829 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom4610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3340 Fin15AnchoredAtom3343 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3449 Fin15AnchoredAtom4610 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29830 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom4611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3340 Fin15AnchoredAtom3344 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3450 Fin15AnchoredAtom4611 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29831 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom4615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3342 Fin15AnchoredAtom3343 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3454 Fin15AnchoredAtom4615 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29832 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom4616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3342 Fin15AnchoredAtom3344 Fin15AnchoredAtom3353
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3455 Fin15AnchoredAtom4616 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29833 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom4617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3343 Fin15AnchoredAtom3344 Fin15AnchoredAtom3354
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3456 Fin15AnchoredAtom4617 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29834 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom4621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3346 Fin15AnchoredAtom3347 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3404 Fin15AnchoredAtom3460 Fin15AnchoredAtom4621 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29835 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom4622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3346 Fin15AnchoredAtom3348 Fin15AnchoredAtom3353
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3461 Fin15AnchoredAtom4622 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29836 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom4623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3347 Fin15AnchoredAtom3348 Fin15AnchoredAtom3354
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3462 Fin15AnchoredAtom4623 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29837 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom4627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3352 Fin15AnchoredAtom3353 Fin15AnchoredAtom3354
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3466 Fin15AnchoredAtom4627 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 6, 13, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29838 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3355 chi ∧
      Fin15AnchoredAtom3356 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3376 chi ∧
      Fin15AnchoredAtom3467 chi ∧
      Fin15AnchoredAtom4628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3355 Fin15AnchoredAtom3356 Fin15AnchoredAtom3361
    Fin15AnchoredAtom3376 Fin15AnchoredAtom3467 Fin15AnchoredAtom4628 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 10}, {1, 7, 8, 9, 10}, {1, 5, 8, 9, 10}, {1, 5, 7, 9, 10}, {1, 5, 7, 8, 10}, {1, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29839 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom4644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3361 Fin15AnchoredAtom3363 Fin15AnchoredAtom3367
    Fin15AnchoredAtom3392 Fin15AnchoredAtom3483 Fin15AnchoredAtom4644 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {1, 7, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 7, 9, 12}, {1, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29840 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom4645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3361 Fin15AnchoredAtom3364 Fin15AnchoredAtom3368
    Fin15AnchoredAtom3393 Fin15AnchoredAtom3484 Fin15AnchoredAtom4645 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {1, 7, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29841 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom4646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3361 Fin15AnchoredAtom3365 Fin15AnchoredAtom3369
    Fin15AnchoredAtom3394 Fin15AnchoredAtom3485 Fin15AnchoredAtom4646 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {1, 7, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29842 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom4650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3363 Fin15AnchoredAtom3364 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3398 Fin15AnchoredAtom3489 Fin15AnchoredAtom4650 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {1, 7, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 9, 13}, {1, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29843 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom4651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3363 Fin15AnchoredAtom3365 Fin15AnchoredAtom3374
    Fin15AnchoredAtom3399 Fin15AnchoredAtom3490 Fin15AnchoredAtom4651 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {1, 7, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29844 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom4652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3364 Fin15AnchoredAtom3365 Fin15AnchoredAtom3375
    Fin15AnchoredAtom3400 Fin15AnchoredAtom3491 Fin15AnchoredAtom4652 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {1, 7, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 9, 14}, {1, 5, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29845 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom4656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3367 Fin15AnchoredAtom3368 Fin15AnchoredAtom3373
    Fin15AnchoredAtom3404 Fin15AnchoredAtom3495 Fin15AnchoredAtom4656 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 7, 10, 13}, {1, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29846 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom4657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3367 Fin15AnchoredAtom3369 Fin15AnchoredAtom3374
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3496 Fin15AnchoredAtom4657 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29847 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom4658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3368 Fin15AnchoredAtom3369 Fin15AnchoredAtom3375
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3497 Fin15AnchoredAtom4658 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 10, 14}, {1, 5, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29848 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom4662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3373 Fin15AnchoredAtom3374 Fin15AnchoredAtom3375
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3501 Fin15AnchoredAtom4662 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 7, 13, 14}, {1, 5, 7, 12, 14}, {1, 5, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29849 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3382 chi ∧
      Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom4676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3382 Fin15AnchoredAtom3383 Fin15AnchoredAtom3388
    Fin15AnchoredAtom3404 Fin15AnchoredAtom3515 Fin15AnchoredAtom4676 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 10, 12, 13}, {1, 8, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 8, 12, 13}, {1, 5, 8, 10, 13}, {1, 5, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29850 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3392 Fin15AnchoredAtom3393 Fin15AnchoredAtom3398
    Fin15AnchoredAtom3404 Fin15AnchoredAtom3525 Fin15AnchoredAtom4686 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {1, 9, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 5, 9, 12, 13}, {1, 5, 9, 10, 13}, {1, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29851 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3392 Fin15AnchoredAtom3394 Fin15AnchoredAtom3399
    Fin15AnchoredAtom3405 Fin15AnchoredAtom3526 Fin15AnchoredAtom4687 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {1, 9, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29852 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3393 Fin15AnchoredAtom3394 Fin15AnchoredAtom3400
    Fin15AnchoredAtom3406 Fin15AnchoredAtom3527 Fin15AnchoredAtom4688 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {1, 9, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 10, 14}, {1, 5, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29853 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3398 Fin15AnchoredAtom3399 Fin15AnchoredAtom3400
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3531 Fin15AnchoredAtom4692 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 9, 13, 14}, {1, 5, 9, 12, 14}, {1, 5, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29854 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3404 Fin15AnchoredAtom3405 Fin15AnchoredAtom3406
    Fin15AnchoredAtom3410 Fin15AnchoredAtom3535 Fin15AnchoredAtom4696 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {1, 10, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 5, 10, 13, 14}, {1, 5, 10, 12, 14}, {1, 5, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29855 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3412 chi ∧
      Fin15AnchoredAtom3414 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3438 chi ∧
      Fin15AnchoredAtom3473 chi ∧
      Fin15AnchoredAtom4704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3412 Fin15AnchoredAtom3414 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3438 Fin15AnchoredAtom3473 Fin15AnchoredAtom4704 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 12}, {1, 7, 8, 10, 12}, {1, 6, 8, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 8, 12}, {1, 6, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29856 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3414 chi ∧
      Fin15AnchoredAtom3415 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom3479 chi ∧
      Fin15AnchoredAtom4710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3414 Fin15AnchoredAtom3415 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3444 Fin15AnchoredAtom3479 Fin15AnchoredAtom4710 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 12, 13}, {1, 7, 8, 12, 13}, {1, 6, 8, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 8, 13}, {1, 6, 7, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29857 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom4714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3417 Fin15AnchoredAtom3419 Fin15AnchoredAtom3423
    Fin15AnchoredAtom3448 Fin15AnchoredAtom3483 Fin15AnchoredAtom4714 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {1, 7, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 6, 7, 10, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29858 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom4715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3417 Fin15AnchoredAtom3420 Fin15AnchoredAtom3424
    Fin15AnchoredAtom3449 Fin15AnchoredAtom3484 Fin15AnchoredAtom4715 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {1, 7, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29859 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom4716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3417 Fin15AnchoredAtom3421 Fin15AnchoredAtom3425
    Fin15AnchoredAtom3450 Fin15AnchoredAtom3485 Fin15AnchoredAtom4716 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {1, 7, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29860 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3418 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3426 chi ∧
      Fin15AnchoredAtom3451 chi ∧
      Fin15AnchoredAtom3486 chi ∧
      Fin15AnchoredAtom4717 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3418 Fin15AnchoredAtom3419 Fin15AnchoredAtom3426
    Fin15AnchoredAtom3451 Fin15AnchoredAtom3486 Fin15AnchoredAtom4717 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 11, 12}, {1, 7, 9, 11, 12}, {1, 6, 9, 11, 12}, {1, 6, 7, 11, 12}, {1, 6, 7, 9, 12}, {1, 6, 7, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29861 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom4720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3419 Fin15AnchoredAtom3420 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3489 Fin15AnchoredAtom4720 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {1, 7, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 9, 13}, {1, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29862 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom4721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3419 Fin15AnchoredAtom3421 Fin15AnchoredAtom3430
    Fin15AnchoredAtom3455 Fin15AnchoredAtom3490 Fin15AnchoredAtom4721 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {1, 7, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29863 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom4722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3420 Fin15AnchoredAtom3421 Fin15AnchoredAtom3431
    Fin15AnchoredAtom3456 Fin15AnchoredAtom3491 Fin15AnchoredAtom4722 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {1, 7, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 9, 14}, {1, 6, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29864 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom4726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3423 Fin15AnchoredAtom3424 Fin15AnchoredAtom3429
    Fin15AnchoredAtom3460 Fin15AnchoredAtom3495 Fin15AnchoredAtom4726 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 7, 12, 13}, {1, 6, 7, 10, 13}, {1, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29865 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom4727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3423 Fin15AnchoredAtom3425 Fin15AnchoredAtom3430
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3496 Fin15AnchoredAtom4727 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29866 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom4728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3424 Fin15AnchoredAtom3425 Fin15AnchoredAtom3431
    Fin15AnchoredAtom3462 Fin15AnchoredAtom3497 Fin15AnchoredAtom4728 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 10, 14}, {1, 6, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29867 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom4732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3429 Fin15AnchoredAtom3430 Fin15AnchoredAtom3431
    Fin15AnchoredAtom3466 Fin15AnchoredAtom3501 Fin15AnchoredAtom4732 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 7, 13, 14}, {1, 6, 7, 12, 14}, {1, 6, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29868 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3434 chi ∧
      Fin15AnchoredAtom3435 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom4740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3434 Fin15AnchoredAtom3435 Fin15AnchoredAtom3444
    Fin15AnchoredAtom3454 Fin15AnchoredAtom3509 Fin15AnchoredAtom4740 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 9, 12, 13}, {1, 8, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 8, 12, 13}, {1, 6, 8, 9, 13}, {1, 6, 8, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29869 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3438 chi ∧
      Fin15AnchoredAtom3439 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom4746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3438 Fin15AnchoredAtom3439 Fin15AnchoredAtom3444
    Fin15AnchoredAtom3460 Fin15AnchoredAtom3515 Fin15AnchoredAtom4746 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 13}, {1, 8, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 8, 12, 13}, {1, 6, 8, 10, 13}, {1, 6, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29870 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3448 Fin15AnchoredAtom3449 Fin15AnchoredAtom3454
    Fin15AnchoredAtom3460 Fin15AnchoredAtom3525 Fin15AnchoredAtom4756 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {1, 9, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 6, 9, 12, 13}, {1, 6, 9, 10, 13}, {1, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29871 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3448 Fin15AnchoredAtom3450 Fin15AnchoredAtom3455
    Fin15AnchoredAtom3461 Fin15AnchoredAtom3526 Fin15AnchoredAtom4757 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {1, 9, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29872 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3449 Fin15AnchoredAtom3450 Fin15AnchoredAtom3456
    Fin15AnchoredAtom3462 Fin15AnchoredAtom3527 Fin15AnchoredAtom4758 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {1, 9, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 10, 14}, {1, 6, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29873 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3454 Fin15AnchoredAtom3455 Fin15AnchoredAtom3456
    Fin15AnchoredAtom3466 Fin15AnchoredAtom3531 Fin15AnchoredAtom4762 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 9, 13, 14}, {1, 6, 9, 12, 14}, {1, 6, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29874 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3460 Fin15AnchoredAtom3461 Fin15AnchoredAtom3462
    Fin15AnchoredAtom3466 Fin15AnchoredAtom3535 Fin15AnchoredAtom4766 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 6, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {1, 10, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 6, 10, 13, 14}, {1, 6, 10, 12, 14}, {1, 6, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29875 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3483 Fin15AnchoredAtom3484 Fin15AnchoredAtom3489
    Fin15AnchoredAtom3495 Fin15AnchoredAtom3525 Fin15AnchoredAtom4791 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 7, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {1, 9, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 7, 9, 12, 13}, {1, 7, 9, 10, 13}, {1, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29876 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3483 Fin15AnchoredAtom3485 Fin15AnchoredAtom3490
    Fin15AnchoredAtom3496 Fin15AnchoredAtom3526 Fin15AnchoredAtom4792 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 7, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {1, 9, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29877 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3484 Fin15AnchoredAtom3485 Fin15AnchoredAtom3491
    Fin15AnchoredAtom3497 Fin15AnchoredAtom3527 Fin15AnchoredAtom4793 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 7, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {1, 9, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 10, 14}, {1, 7, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29878 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3489 Fin15AnchoredAtom3490 Fin15AnchoredAtom3491
    Fin15AnchoredAtom3501 Fin15AnchoredAtom3531 Fin15AnchoredAtom4797 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 7, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 9, 13, 14}, {1, 7, 9, 12, 14}, {1, 7, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29879 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3495 Fin15AnchoredAtom3496 Fin15AnchoredAtom3497
    Fin15AnchoredAtom3501 Fin15AnchoredAtom3535 Fin15AnchoredAtom4801 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 7, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {1, 10, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 7, 10, 13, 14}, {1, 7, 10, 12, 14}, {1, 7, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29880 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3503 chi ∧
      Fin15AnchoredAtom3504 chi ∧
      Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3503 Fin15AnchoredAtom3504 Fin15AnchoredAtom3509
    Fin15AnchoredAtom3515 Fin15AnchoredAtom3525 Fin15AnchoredAtom4806 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 8, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 8, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{8, 9, 10, 12, 13}, {1, 9, 10, 12, 13}, {1, 8, 10, 12, 13}, {1, 8, 9, 12, 13}, {1, 8, 9, 10, 13}, {1, 8, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29881 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3525 Fin15AnchoredAtom3526 Fin15AnchoredAtom3527
    Fin15AnchoredAtom3531 Fin15AnchoredAtom3535 Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 9, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {1, 10, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 9, 10, 13, 14}, {1, 9, 10, 12, 14}, {1, 9, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29882 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom4032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3538 Fin15AnchoredAtom3546
    Fin15AnchoredAtom3582 Fin15AnchoredAtom3702 Fin15AnchoredAtom4032 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 7}, {2, 4, 5, 6, 7}, {2, 3, 5, 6, 7}, {2, 3, 4, 6, 7}, {2, 3, 4, 5, 7}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29883 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom4034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3540 Fin15AnchoredAtom3548
    Fin15AnchoredAtom3584 Fin15AnchoredAtom3704 Fin15AnchoredAtom4034 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 9}, {2, 4, 5, 6, 9}, {2, 3, 5, 6, 9}, {2, 3, 4, 6, 9}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29884 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom4035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3541 Fin15AnchoredAtom3549
    Fin15AnchoredAtom3585 Fin15AnchoredAtom3705 Fin15AnchoredAtom4035 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 10}, {2, 4, 5, 6, 10}, {2, 3, 5, 6, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29885 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom4037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3543 Fin15AnchoredAtom3551
    Fin15AnchoredAtom3587 Fin15AnchoredAtom3707 Fin15AnchoredAtom4037 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 12}, {2, 4, 5, 6, 12}, {2, 3, 5, 6, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29886 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom4038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3544 Fin15AnchoredAtom3552
    Fin15AnchoredAtom3588 Fin15AnchoredAtom3708 Fin15AnchoredAtom4038 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 13}, {2, 4, 5, 6, 13}, {2, 3, 5, 6, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29887 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3537 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom4039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3537 Fin15AnchoredAtom3545 Fin15AnchoredAtom3553
    Fin15AnchoredAtom3589 Fin15AnchoredAtom3709 Fin15AnchoredAtom4039 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 14}, {2, 4, 5, 6, 14}, {2, 3, 5, 6, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29888 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom4041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3540 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3591 Fin15AnchoredAtom3711 Fin15AnchoredAtom4041 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 9}, {2, 4, 5, 7, 9}, {2, 3, 5, 7, 9}, {2, 3, 4, 7, 9}, {2, 3, 4, 5, 9}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29889 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom4042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3541 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3592 Fin15AnchoredAtom3712 Fin15AnchoredAtom4042 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 10}, {2, 4, 5, 7, 10}, {2, 3, 5, 7, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29890 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom4044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3543 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3594 Fin15AnchoredAtom3714 Fin15AnchoredAtom4044 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 12}, {2, 4, 5, 7, 12}, {2, 3, 5, 7, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29891 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom4045 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3544 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3595 Fin15AnchoredAtom3715 Fin15AnchoredAtom4045 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 13}, {2, 4, 5, 7, 13}, {2, 3, 5, 7, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29892 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3538 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom4046 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3538 Fin15AnchoredAtom3545 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3596 Fin15AnchoredAtom3716 Fin15AnchoredAtom4046 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 14}, {2, 4, 5, 7, 14}, {2, 3, 5, 7, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29893 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom4053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3540 Fin15AnchoredAtom3541 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3603 Fin15AnchoredAtom3723 Fin15AnchoredAtom4053 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 10}, {2, 4, 5, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 4, 9, 10}, {2, 3, 4, 5, 10}, {2, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29894 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom4055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3540 Fin15AnchoredAtom3543 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3605 Fin15AnchoredAtom3725 Fin15AnchoredAtom4055 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 12}, {2, 4, 5, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29895 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom4056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3540 Fin15AnchoredAtom3544 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3606 Fin15AnchoredAtom3726 Fin15AnchoredAtom4056 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 13}, {2, 4, 5, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29896 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3540 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom4057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3540 Fin15AnchoredAtom3545 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3607 Fin15AnchoredAtom3727 Fin15AnchoredAtom4057 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 14}, {2, 4, 5, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29897 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom4059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3541 Fin15AnchoredAtom3543 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3609 Fin15AnchoredAtom3729 Fin15AnchoredAtom4059 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 12}, {2, 4, 5, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 4, 10, 12}, {2, 3, 4, 5, 12}, {2, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29898 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom4060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3541 Fin15AnchoredAtom3544 Fin15AnchoredAtom3574
    Fin15AnchoredAtom3610 Fin15AnchoredAtom3730 Fin15AnchoredAtom4060 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 13}, {2, 4, 5, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29899 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3541 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom4061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3541 Fin15AnchoredAtom3545 Fin15AnchoredAtom3575
    Fin15AnchoredAtom3611 Fin15AnchoredAtom3731 Fin15AnchoredAtom4061 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 14}, {2, 4, 5, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29900 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom4065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3543 Fin15AnchoredAtom3544 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3615 Fin15AnchoredAtom3735 Fin15AnchoredAtom4065 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 12, 13}, {2, 4, 5, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 5, 13}, {2, 3, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29901 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3543 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom4066 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3543 Fin15AnchoredAtom3545 Fin15AnchoredAtom3580
    Fin15AnchoredAtom3616 Fin15AnchoredAtom3736 Fin15AnchoredAtom4066 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 12, 14}, {2, 4, 5, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29902 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3544 chi ∧
      Fin15AnchoredAtom3545 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom4067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3544 Fin15AnchoredAtom3545 Fin15AnchoredAtom3581
    Fin15AnchoredAtom3617 Fin15AnchoredAtom3737 Fin15AnchoredAtom4067 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 13, 14}, {2, 4, 5, 13, 14}, {2, 3, 5, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 5, 14}, {2, 3, 4, 5, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29903 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom4069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3548 Fin15AnchoredAtom3555
    Fin15AnchoredAtom3619 Fin15AnchoredAtom3739 Fin15AnchoredAtom4069 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 9}, {2, 4, 6, 7, 9}, {2, 3, 6, 7, 9}, {2, 3, 4, 7, 9}, {2, 3, 4, 6, 9}, {2, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29904 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom4070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3549 Fin15AnchoredAtom3556
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3740 Fin15AnchoredAtom4070 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 10}, {2, 4, 6, 7, 10}, {2, 3, 6, 7, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29905 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom4072 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3551 Fin15AnchoredAtom3558
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3742 Fin15AnchoredAtom4072 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 12}, {2, 4, 6, 7, 12}, {2, 3, 6, 7, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29906 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom4073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3552 Fin15AnchoredAtom3559
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3743 Fin15AnchoredAtom4073 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 13}, {2, 4, 6, 7, 13}, {2, 3, 6, 7, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29907 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3546 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom4074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3546 Fin15AnchoredAtom3553 Fin15AnchoredAtom3560
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3744 Fin15AnchoredAtom4074 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 14}, {2, 4, 6, 7, 14}, {2, 3, 6, 7, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29908 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom4081 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3548 Fin15AnchoredAtom3549 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3631 Fin15AnchoredAtom3751 Fin15AnchoredAtom4081 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 10}, {2, 4, 6, 9, 10}, {2, 3, 6, 9, 10}, {2, 3, 4, 9, 10}, {2, 3, 4, 6, 10}, {2, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29909 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom4083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3548 Fin15AnchoredAtom3551 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3753 Fin15AnchoredAtom4083 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 12}, {2, 4, 6, 9, 12}, {2, 3, 6, 9, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29910 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom4084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3548 Fin15AnchoredAtom3552 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3754 Fin15AnchoredAtom4084 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 13}, {2, 4, 6, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29911 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3548 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom4085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3548 Fin15AnchoredAtom3553 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3755 Fin15AnchoredAtom4085 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 14}, {2, 4, 6, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29912 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom4087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3549 Fin15AnchoredAtom3551 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3757 Fin15AnchoredAtom4087 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 12}, {2, 4, 6, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 4, 10, 12}, {2, 3, 4, 6, 12}, {2, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29913 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom4088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3549 Fin15AnchoredAtom3552 Fin15AnchoredAtom3574
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3758 Fin15AnchoredAtom4088 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 13}, {2, 4, 6, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29914 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3549 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom4089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3549 Fin15AnchoredAtom3553 Fin15AnchoredAtom3575
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3759 Fin15AnchoredAtom4089 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 14}, {2, 4, 6, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29915 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom4093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3551 Fin15AnchoredAtom3552 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3763 Fin15AnchoredAtom4093 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 12, 13}, {2, 4, 6, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 6, 13}, {2, 3, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29916 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3551 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom4094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3551 Fin15AnchoredAtom3553 Fin15AnchoredAtom3580
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3764 Fin15AnchoredAtom4094 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 12, 14}, {2, 4, 6, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29917 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3552 chi ∧
      Fin15AnchoredAtom3553 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom4095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3552 Fin15AnchoredAtom3553 Fin15AnchoredAtom3581
    Fin15AnchoredAtom3645 Fin15AnchoredAtom3765 Fin15AnchoredAtom4095 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 13, 14}, {2, 4, 6, 13, 14}, {2, 3, 6, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 6, 14}, {2, 3, 4, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29918 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom4102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3555 Fin15AnchoredAtom3556 Fin15AnchoredAtom3567
    Fin15AnchoredAtom3652 Fin15AnchoredAtom3772 Fin15AnchoredAtom4102 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 10}, {2, 4, 7, 9, 10}, {2, 3, 7, 9, 10}, {2, 3, 4, 9, 10}, {2, 3, 4, 7, 10}, {2, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29919 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom4104 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3555 Fin15AnchoredAtom3558 Fin15AnchoredAtom3569
    Fin15AnchoredAtom3654 Fin15AnchoredAtom3774 Fin15AnchoredAtom4104 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 12}, {2, 4, 7, 9, 12}, {2, 3, 7, 9, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29920 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom4105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3555 Fin15AnchoredAtom3559 Fin15AnchoredAtom3570
    Fin15AnchoredAtom3655 Fin15AnchoredAtom3775 Fin15AnchoredAtom4105 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 13}, {2, 4, 7, 9, 13}, {2, 3, 7, 9, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29921 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3555 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom4106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3555 Fin15AnchoredAtom3560 Fin15AnchoredAtom3571
    Fin15AnchoredAtom3656 Fin15AnchoredAtom3776 Fin15AnchoredAtom4106 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 14}, {2, 4, 7, 9, 14}, {2, 3, 7, 9, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29922 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom4108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3556 Fin15AnchoredAtom3558 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3658 Fin15AnchoredAtom3778 Fin15AnchoredAtom4108 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 12}, {2, 4, 7, 10, 12}, {2, 3, 7, 10, 12}, {2, 3, 4, 10, 12}, {2, 3, 4, 7, 12}, {2, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29923 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom4109 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3556 Fin15AnchoredAtom3559 Fin15AnchoredAtom3574
    Fin15AnchoredAtom3659 Fin15AnchoredAtom3779 Fin15AnchoredAtom4109 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 13}, {2, 4, 7, 10, 13}, {2, 3, 7, 10, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29924 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3556 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom4110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3556 Fin15AnchoredAtom3560 Fin15AnchoredAtom3575
    Fin15AnchoredAtom3660 Fin15AnchoredAtom3780 Fin15AnchoredAtom4110 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 14}, {2, 4, 7, 10, 14}, {2, 3, 7, 10, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29925 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom4114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3558 Fin15AnchoredAtom3559 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3664 Fin15AnchoredAtom3784 Fin15AnchoredAtom4114 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 12, 13}, {2, 4, 7, 12, 13}, {2, 3, 7, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 7, 13}, {2, 3, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29926 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3558 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom4115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3558 Fin15AnchoredAtom3560 Fin15AnchoredAtom3580
    Fin15AnchoredAtom3665 Fin15AnchoredAtom3785 Fin15AnchoredAtom4115 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 12, 14}, {2, 4, 7, 12, 14}, {2, 3, 7, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29927 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3559 chi ∧
      Fin15AnchoredAtom3560 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom4116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3559 Fin15AnchoredAtom3560 Fin15AnchoredAtom3581
    Fin15AnchoredAtom3666 Fin15AnchoredAtom3786 Fin15AnchoredAtom4116 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 13, 14}, {2, 4, 7, 13, 14}, {2, 3, 7, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 7, 14}, {2, 3, 4, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29928 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom4133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3567 Fin15AnchoredAtom3569 Fin15AnchoredAtom3573
    Fin15AnchoredAtom3683 Fin15AnchoredAtom3803 Fin15AnchoredAtom4133 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 12}, {2, 4, 9, 10, 12}, {2, 3, 9, 10, 12}, {2, 3, 4, 10, 12}, {2, 3, 4, 9, 12}, {2, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29929 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom4134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3567 Fin15AnchoredAtom3570 Fin15AnchoredAtom3574
    Fin15AnchoredAtom3684 Fin15AnchoredAtom3804 Fin15AnchoredAtom4134 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 13}, {2, 4, 9, 10, 13}, {2, 3, 9, 10, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29930 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3567 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom3805 chi ∧
      Fin15AnchoredAtom4135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3567 Fin15AnchoredAtom3571 Fin15AnchoredAtom3575
    Fin15AnchoredAtom3685 Fin15AnchoredAtom3805 Fin15AnchoredAtom4135 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 14}, {2, 4, 9, 10, 14}, {2, 3, 9, 10, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29931 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom3809 chi ∧
      Fin15AnchoredAtom4139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3569 Fin15AnchoredAtom3570 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3689 Fin15AnchoredAtom3809 Fin15AnchoredAtom4139 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 12, 13}, {2, 4, 9, 12, 13}, {2, 3, 9, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 9, 13}, {2, 3, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29932 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3569 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom3810 chi ∧
      Fin15AnchoredAtom4140 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3569 Fin15AnchoredAtom3571 Fin15AnchoredAtom3580
    Fin15AnchoredAtom3690 Fin15AnchoredAtom3810 Fin15AnchoredAtom4140 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 12, 14}, {2, 4, 9, 12, 14}, {2, 3, 9, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29933 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3570 chi ∧
      Fin15AnchoredAtom3571 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom3811 chi ∧
      Fin15AnchoredAtom4141 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3570 Fin15AnchoredAtom3571 Fin15AnchoredAtom3581
    Fin15AnchoredAtom3691 Fin15AnchoredAtom3811 Fin15AnchoredAtom4141 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 13, 14}, {2, 4, 9, 13, 14}, {2, 3, 9, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 9, 14}, {2, 3, 4, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29934 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom3815 chi ∧
      Fin15AnchoredAtom4145 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3573 Fin15AnchoredAtom3574 Fin15AnchoredAtom3579
    Fin15AnchoredAtom3695 Fin15AnchoredAtom3815 Fin15AnchoredAtom4145 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 12, 13}, {2, 4, 10, 12, 13}, {2, 3, 10, 12, 13}, {2, 3, 4, 12, 13}, {2, 3, 4, 10, 13}, {2, 3, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29935 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3573 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom3816 chi ∧
      Fin15AnchoredAtom4146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3573 Fin15AnchoredAtom3575 Fin15AnchoredAtom3580
    Fin15AnchoredAtom3696 Fin15AnchoredAtom3816 Fin15AnchoredAtom4146 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 12, 14}, {2, 4, 10, 12, 14}, {2, 3, 10, 12, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29936 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3574 chi ∧
      Fin15AnchoredAtom3575 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom3817 chi ∧
      Fin15AnchoredAtom4147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3574 Fin15AnchoredAtom3575 Fin15AnchoredAtom3581
    Fin15AnchoredAtom3697 Fin15AnchoredAtom3817 Fin15AnchoredAtom4147 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 13, 14}, {2, 4, 10, 13, 14}, {2, 3, 10, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 10, 14}, {2, 3, 4, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29937 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3579 chi ∧
      Fin15AnchoredAtom3580 chi ∧
      Fin15AnchoredAtom3581 chi ∧
      Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom3821 chi ∧
      Fin15AnchoredAtom4151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3579 Fin15AnchoredAtom3580 Fin15AnchoredAtom3581
    Fin15AnchoredAtom3701 Fin15AnchoredAtom3821 Fin15AnchoredAtom4151 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 4, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 12, 13, 14}, {2, 4, 12, 13, 14}, {2, 3, 12, 13, 14}, {2, 3, 4, 13, 14}, {2, 3, 4, 12, 14}, {2, 3, 4, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29938 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3591 chi ∧
      Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom3823 chi ∧
      Fin15AnchoredAtom4153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3584 Fin15AnchoredAtom3591
    Fin15AnchoredAtom3619 Fin15AnchoredAtom3823 Fin15AnchoredAtom4153 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 9}, {2, 5, 6, 7, 9}, {2, 3, 6, 7, 9}, {2, 3, 5, 7, 9}, {2, 3, 5, 6, 9}, {2, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29939 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3592 chi ∧
      Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom3824 chi ∧
      Fin15AnchoredAtom4154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3585 Fin15AnchoredAtom3592
    Fin15AnchoredAtom3620 Fin15AnchoredAtom3824 Fin15AnchoredAtom4154 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 10}, {2, 5, 6, 7, 10}, {2, 3, 6, 7, 10}, {2, 3, 5, 7, 10}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29940 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom3826 chi ∧
      Fin15AnchoredAtom4156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3587 Fin15AnchoredAtom3594
    Fin15AnchoredAtom3622 Fin15AnchoredAtom3826 Fin15AnchoredAtom4156 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 12}, {2, 5, 6, 7, 12}, {2, 3, 6, 7, 12}, {2, 3, 5, 7, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29941 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom3827 chi ∧
      Fin15AnchoredAtom4157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3588 Fin15AnchoredAtom3595
    Fin15AnchoredAtom3623 Fin15AnchoredAtom3827 Fin15AnchoredAtom4157 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 13}, {2, 5, 6, 7, 13}, {2, 3, 6, 7, 13}, {2, 3, 5, 7, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29942 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3582 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom3828 chi ∧
      Fin15AnchoredAtom4158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3582 Fin15AnchoredAtom3589 Fin15AnchoredAtom3596
    Fin15AnchoredAtom3624 Fin15AnchoredAtom3828 Fin15AnchoredAtom4158 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 14}, {2, 5, 6, 7, 14}, {2, 3, 6, 7, 14}, {2, 3, 5, 7, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29943 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom3835 chi ∧
      Fin15AnchoredAtom4165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3584 Fin15AnchoredAtom3585 Fin15AnchoredAtom3603
    Fin15AnchoredAtom3631 Fin15AnchoredAtom3835 Fin15AnchoredAtom4165 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 10}, {2, 5, 6, 9, 10}, {2, 3, 6, 9, 10}, {2, 3, 5, 9, 10}, {2, 3, 5, 6, 10}, {2, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29944 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom3837 chi ∧
      Fin15AnchoredAtom4167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3584 Fin15AnchoredAtom3587 Fin15AnchoredAtom3605
    Fin15AnchoredAtom3633 Fin15AnchoredAtom3837 Fin15AnchoredAtom4167 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 12}, {2, 5, 6, 9, 12}, {2, 3, 6, 9, 12}, {2, 3, 5, 9, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29945 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom3838 chi ∧
      Fin15AnchoredAtom4168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3584 Fin15AnchoredAtom3588 Fin15AnchoredAtom3606
    Fin15AnchoredAtom3634 Fin15AnchoredAtom3838 Fin15AnchoredAtom4168 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 13}, {2, 5, 6, 9, 13}, {2, 3, 6, 9, 13}, {2, 3, 5, 9, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29946 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3584 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom3839 chi ∧
      Fin15AnchoredAtom4169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3584 Fin15AnchoredAtom3589 Fin15AnchoredAtom3607
    Fin15AnchoredAtom3635 Fin15AnchoredAtom3839 Fin15AnchoredAtom4169 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 14}, {2, 5, 6, 9, 14}, {2, 3, 6, 9, 14}, {2, 3, 5, 9, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29947 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom3841 chi ∧
      Fin15AnchoredAtom4171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3585 Fin15AnchoredAtom3587 Fin15AnchoredAtom3609
    Fin15AnchoredAtom3637 Fin15AnchoredAtom3841 Fin15AnchoredAtom4171 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 12}, {2, 5, 6, 10, 12}, {2, 3, 6, 10, 12}, {2, 3, 5, 10, 12}, {2, 3, 5, 6, 12}, {2, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29948 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom3842 chi ∧
      Fin15AnchoredAtom4172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3585 Fin15AnchoredAtom3588 Fin15AnchoredAtom3610
    Fin15AnchoredAtom3638 Fin15AnchoredAtom3842 Fin15AnchoredAtom4172 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 13}, {2, 5, 6, 10, 13}, {2, 3, 6, 10, 13}, {2, 3, 5, 10, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29949 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3585 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom3843 chi ∧
      Fin15AnchoredAtom4173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3585 Fin15AnchoredAtom3589 Fin15AnchoredAtom3611
    Fin15AnchoredAtom3639 Fin15AnchoredAtom3843 Fin15AnchoredAtom4173 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 14}, {2, 5, 6, 10, 14}, {2, 3, 6, 10, 14}, {2, 3, 5, 10, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29950 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3588 chi ∧
      Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom3847 chi ∧
      Fin15AnchoredAtom4177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3587 Fin15AnchoredAtom3588 Fin15AnchoredAtom3615
    Fin15AnchoredAtom3643 Fin15AnchoredAtom3847 Fin15AnchoredAtom4177 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 12, 13}, {2, 5, 6, 12, 13}, {2, 3, 6, 12, 13}, {2, 3, 5, 12, 13}, {2, 3, 5, 6, 13}, {2, 3, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29951 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3587 chi ∧
      Fin15AnchoredAtom3589 chi ∧
      Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom3848 chi ∧
      Fin15AnchoredAtom4178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3587 Fin15AnchoredAtom3589 Fin15AnchoredAtom3616
    Fin15AnchoredAtom3644 Fin15AnchoredAtom3848 Fin15AnchoredAtom4178 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{2, 3, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({2, 3, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({2, 3, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 12, 14}, {2, 5, 6, 12, 14}, {2, 3, 6, 12, 14}, {2, 3, 5, 12, 14}, {2, 3, 5, 6, 14}, {2, 3, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
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
