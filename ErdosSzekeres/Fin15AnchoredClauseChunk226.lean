module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 226. -/

theorem fin15Anchored_clause28928 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom4088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2339 Fin15AnchoredAtom2342 Fin15AnchoredAtom2364
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2548 Fin15AnchoredAtom4088 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 13}, {0, 4, 6, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28929 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom4089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2339 Fin15AnchoredAtom2343 Fin15AnchoredAtom2365
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2549 Fin15AnchoredAtom4089 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 14}, {0, 4, 6, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28930 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom4093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2341 Fin15AnchoredAtom2342 Fin15AnchoredAtom2369
    Fin15AnchoredAtom2433 Fin15AnchoredAtom2553 Fin15AnchoredAtom4093 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 12, 13}, {0, 4, 6, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28931 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom4094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2341 Fin15AnchoredAtom2343 Fin15AnchoredAtom2370
    Fin15AnchoredAtom2434 Fin15AnchoredAtom2554 Fin15AnchoredAtom4094 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 12, 14}, {0, 4, 6, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28932 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom4095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2342 Fin15AnchoredAtom2343 Fin15AnchoredAtom2371
    Fin15AnchoredAtom2435 Fin15AnchoredAtom2555 Fin15AnchoredAtom4095 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 13, 14}, {0, 4, 6, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28933 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom4096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2344 Fin15AnchoredAtom2345 Fin15AnchoredAtom2351
    Fin15AnchoredAtom2436 Fin15AnchoredAtom2556 Fin15AnchoredAtom4096 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 8, 9}, {0, 4, 7, 8, 9}, {0, 3, 7, 8, 9}, {0, 3, 4, 8, 9}, {0, 3, 4, 7, 9}, {0, 3, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28934 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom4097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2344 Fin15AnchoredAtom2346 Fin15AnchoredAtom2352
    Fin15AnchoredAtom2437 Fin15AnchoredAtom2557 Fin15AnchoredAtom4097 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 8, 10}, {0, 4, 7, 8, 10}, {0, 3, 7, 8, 10}, {0, 3, 4, 8, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28935 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom4099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2344 Fin15AnchoredAtom2348 Fin15AnchoredAtom2354
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2559 Fin15AnchoredAtom4099 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 8, 12}, {0, 4, 7, 8, 12}, {0, 3, 7, 8, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28936 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom4100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2344 Fin15AnchoredAtom2349 Fin15AnchoredAtom2355
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2560 Fin15AnchoredAtom4100 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 8, 13}, {0, 4, 7, 8, 13}, {0, 3, 7, 8, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28937 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom4101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2344 Fin15AnchoredAtom2350 Fin15AnchoredAtom2356
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2561 Fin15AnchoredAtom4101 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 8, 14}, {0, 4, 7, 8, 14}, {0, 3, 7, 8, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28938 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom4102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2345 Fin15AnchoredAtom2346 Fin15AnchoredAtom2357
    Fin15AnchoredAtom2442 Fin15AnchoredAtom2562 Fin15AnchoredAtom4102 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 4, 9, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28939 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom4104 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2345 Fin15AnchoredAtom2348 Fin15AnchoredAtom2359
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2564 Fin15AnchoredAtom4104 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28940 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom4105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2345 Fin15AnchoredAtom2349 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2565 Fin15AnchoredAtom4105 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28941 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom4106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2345 Fin15AnchoredAtom2350 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2566 Fin15AnchoredAtom4106 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28942 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom4108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2346 Fin15AnchoredAtom2348 Fin15AnchoredAtom2363
    Fin15AnchoredAtom2448 Fin15AnchoredAtom2568 Fin15AnchoredAtom4108 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28943 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom4109 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2346 Fin15AnchoredAtom2349 Fin15AnchoredAtom2364
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2569 Fin15AnchoredAtom4109 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28944 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom4110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2346 Fin15AnchoredAtom2350 Fin15AnchoredAtom2365
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2570 Fin15AnchoredAtom4110 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28945 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom4114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2348 Fin15AnchoredAtom2349 Fin15AnchoredAtom2369
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2574 Fin15AnchoredAtom4114 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28946 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom4115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2348 Fin15AnchoredAtom2350 Fin15AnchoredAtom2370
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2575 Fin15AnchoredAtom4115 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28947 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom4116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2349 Fin15AnchoredAtom2350 Fin15AnchoredAtom2371
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2576 Fin15AnchoredAtom4116 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28948 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom4117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2351 Fin15AnchoredAtom2352 Fin15AnchoredAtom2357
    Fin15AnchoredAtom2457 Fin15AnchoredAtom2577 Fin15AnchoredAtom4117 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 9, 10}, {0, 4, 8, 9, 10}, {0, 3, 8, 9, 10}, {0, 3, 4, 9, 10}, {0, 3, 4, 8, 10}, {0, 3, 4, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28949 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom4119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2351 Fin15AnchoredAtom2354 Fin15AnchoredAtom2359
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2579 Fin15AnchoredAtom4119 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 9, 12}, {0, 4, 8, 9, 12}, {0, 3, 8, 9, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28950 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom4120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2351 Fin15AnchoredAtom2355 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2460 Fin15AnchoredAtom2580 Fin15AnchoredAtom4120 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 9, 13}, {0, 4, 8, 9, 13}, {0, 3, 8, 9, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28951 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom4121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2351 Fin15AnchoredAtom2356 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2461 Fin15AnchoredAtom2581 Fin15AnchoredAtom4121 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 9, 14}, {0, 4, 8, 9, 14}, {0, 3, 8, 9, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28952 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom4123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2352 Fin15AnchoredAtom2354 Fin15AnchoredAtom2363
    Fin15AnchoredAtom2463 Fin15AnchoredAtom2583 Fin15AnchoredAtom4123 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 10, 12}, {0, 4, 8, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28953 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom4124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2352 Fin15AnchoredAtom2355 Fin15AnchoredAtom2364
    Fin15AnchoredAtom2464 Fin15AnchoredAtom2584 Fin15AnchoredAtom4124 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 10, 13}, {0, 4, 8, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28954 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom4125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2352 Fin15AnchoredAtom2356 Fin15AnchoredAtom2365
    Fin15AnchoredAtom2465 Fin15AnchoredAtom2585 Fin15AnchoredAtom4125 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 10, 14}, {0, 4, 8, 10, 14}, {0, 3, 8, 10, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28955 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom4129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2354 Fin15AnchoredAtom2355 Fin15AnchoredAtom2369
    Fin15AnchoredAtom2469 Fin15AnchoredAtom2589 Fin15AnchoredAtom4129 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 12, 13}, {0, 4, 8, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28956 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom4130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2354 Fin15AnchoredAtom2356 Fin15AnchoredAtom2370
    Fin15AnchoredAtom2470 Fin15AnchoredAtom2590 Fin15AnchoredAtom4130 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 12, 14}, {0, 4, 8, 12, 14}, {0, 3, 8, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28957 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom4131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2355 Fin15AnchoredAtom2356 Fin15AnchoredAtom2371
    Fin15AnchoredAtom2471 Fin15AnchoredAtom2591 Fin15AnchoredAtom4131 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 13, 14}, {0, 4, 8, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28958 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom4133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2357 Fin15AnchoredAtom2359 Fin15AnchoredAtom2363
    Fin15AnchoredAtom2473 Fin15AnchoredAtom2593 Fin15AnchoredAtom4133 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28959 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom4134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2357 Fin15AnchoredAtom2360 Fin15AnchoredAtom2364
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2594 Fin15AnchoredAtom4134 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28960 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom4135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2357 Fin15AnchoredAtom2361 Fin15AnchoredAtom2365
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2595 Fin15AnchoredAtom4135 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28961 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom4139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2359 Fin15AnchoredAtom2360 Fin15AnchoredAtom2369
    Fin15AnchoredAtom2479 Fin15AnchoredAtom2599 Fin15AnchoredAtom4139 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28962 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom4140 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2359 Fin15AnchoredAtom2361 Fin15AnchoredAtom2370
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2600 Fin15AnchoredAtom4140 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28963 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom4141 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2360 Fin15AnchoredAtom2361 Fin15AnchoredAtom2371
    Fin15AnchoredAtom2481 Fin15AnchoredAtom2601 Fin15AnchoredAtom4141 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28964 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom4145 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2363 Fin15AnchoredAtom2364 Fin15AnchoredAtom2369
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2605 Fin15AnchoredAtom4145 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28965 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom4146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2363 Fin15AnchoredAtom2365 Fin15AnchoredAtom2370
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2606 Fin15AnchoredAtom4146 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28966 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom4147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2364 Fin15AnchoredAtom2365 Fin15AnchoredAtom2371
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2607 Fin15AnchoredAtom4147 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28967 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom4151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2369 Fin15AnchoredAtom2370 Fin15AnchoredAtom2371
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2611 Fin15AnchoredAtom4151 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28968 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom4153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2372 Fin15AnchoredAtom2374 Fin15AnchoredAtom2381
    Fin15AnchoredAtom2409 Fin15AnchoredAtom2613 Fin15AnchoredAtom4153 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 9}, {0, 5, 6, 7, 9}, {0, 3, 6, 7, 9}, {0, 3, 5, 7, 9}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28969 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom4154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2372 Fin15AnchoredAtom2375 Fin15AnchoredAtom2382
    Fin15AnchoredAtom2410 Fin15AnchoredAtom2614 Fin15AnchoredAtom4154 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 10}, {0, 5, 6, 7, 10}, {0, 3, 6, 7, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28970 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom4156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2372 Fin15AnchoredAtom2377 Fin15AnchoredAtom2384
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2616 Fin15AnchoredAtom4156 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 12}, {0, 5, 6, 7, 12}, {0, 3, 6, 7, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28971 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom4157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2372 Fin15AnchoredAtom2378 Fin15AnchoredAtom2385
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2617 Fin15AnchoredAtom4157 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 13}, {0, 5, 6, 7, 13}, {0, 3, 6, 7, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28972 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom4158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2372 Fin15AnchoredAtom2379 Fin15AnchoredAtom2386
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2618 Fin15AnchoredAtom4158 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 14}, {0, 5, 6, 7, 14}, {0, 3, 6, 7, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28973 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom4159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2373 Fin15AnchoredAtom2374 Fin15AnchoredAtom2387
    Fin15AnchoredAtom2415 Fin15AnchoredAtom2619 Fin15AnchoredAtom4159 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 8, 9}, {0, 5, 6, 8, 9}, {0, 3, 6, 8, 9}, {0, 3, 5, 8, 9}, {0, 3, 5, 6, 9}, {0, 3, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28974 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom4164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2373 Fin15AnchoredAtom2379 Fin15AnchoredAtom2392
    Fin15AnchoredAtom2420 Fin15AnchoredAtom2624 Fin15AnchoredAtom4164 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 8, 14}, {0, 5, 6, 8, 14}, {0, 3, 6, 8, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28975 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom4165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2374 Fin15AnchoredAtom2375 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2625 Fin15AnchoredAtom4165 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 10}, {0, 5, 6, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 6, 10}, {0, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28976 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom4167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2374 Fin15AnchoredAtom2377 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2627 Fin15AnchoredAtom4167 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 12}, {0, 5, 6, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28977 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom4168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2374 Fin15AnchoredAtom2378 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2628 Fin15AnchoredAtom4168 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 13}, {0, 5, 6, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28978 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom4169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2374 Fin15AnchoredAtom2379 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2629 Fin15AnchoredAtom4169 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 14}, {0, 5, 6, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28979 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom4171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2375 Fin15AnchoredAtom2377 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2631 Fin15AnchoredAtom4171 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 12}, {0, 5, 6, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 6, 12}, {0, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28980 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom4172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2375 Fin15AnchoredAtom2378 Fin15AnchoredAtom2400
    Fin15AnchoredAtom2428 Fin15AnchoredAtom2632 Fin15AnchoredAtom4172 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 13}, {0, 5, 6, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28981 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom4173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2375 Fin15AnchoredAtom2379 Fin15AnchoredAtom2401
    Fin15AnchoredAtom2429 Fin15AnchoredAtom2633 Fin15AnchoredAtom4173 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 14}, {0, 5, 6, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28982 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom4177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2377 Fin15AnchoredAtom2378 Fin15AnchoredAtom2405
    Fin15AnchoredAtom2433 Fin15AnchoredAtom2637 Fin15AnchoredAtom4177 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 12, 13}, {0, 5, 6, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 6, 13}, {0, 3, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28983 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom4178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2377 Fin15AnchoredAtom2379 Fin15AnchoredAtom2406
    Fin15AnchoredAtom2434 Fin15AnchoredAtom2638 Fin15AnchoredAtom4178 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 12, 14}, {0, 5, 6, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28984 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom4179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2378 Fin15AnchoredAtom2379 Fin15AnchoredAtom2407
    Fin15AnchoredAtom2435 Fin15AnchoredAtom2639 Fin15AnchoredAtom4179 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 13, 14}, {0, 5, 6, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 6, 14}, {0, 3, 5, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28985 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom4180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2380 Fin15AnchoredAtom2381 Fin15AnchoredAtom2387
    Fin15AnchoredAtom2436 Fin15AnchoredAtom2640 Fin15AnchoredAtom4180 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 8, 9}, {0, 5, 7, 8, 9}, {0, 3, 7, 8, 9}, {0, 3, 5, 8, 9}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28986 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2641 chi ∧
      Fin15AnchoredAtom4181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2380 Fin15AnchoredAtom2382 Fin15AnchoredAtom2388
    Fin15AnchoredAtom2437 Fin15AnchoredAtom2641 Fin15AnchoredAtom4181 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 8, 10}, {0, 5, 7, 8, 10}, {0, 3, 7, 8, 10}, {0, 3, 5, 8, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28987 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom4183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2380 Fin15AnchoredAtom2384 Fin15AnchoredAtom2390
    Fin15AnchoredAtom2439 Fin15AnchoredAtom2643 Fin15AnchoredAtom4183 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 8, 12}, {0, 5, 7, 8, 12}, {0, 3, 7, 8, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28988 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom4184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2380 Fin15AnchoredAtom2385 Fin15AnchoredAtom2391
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2644 Fin15AnchoredAtom4184 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 8, 13}, {0, 5, 7, 8, 13}, {0, 3, 7, 8, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28989 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom4185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2380 Fin15AnchoredAtom2386 Fin15AnchoredAtom2392
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2645 Fin15AnchoredAtom4185 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 8, 14}, {0, 5, 7, 8, 14}, {0, 3, 7, 8, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28990 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom4186 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2381 Fin15AnchoredAtom2382 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2442 Fin15AnchoredAtom2646 Fin15AnchoredAtom4186 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 7, 10}, {0, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28991 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom4188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2381 Fin15AnchoredAtom2384 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2648 Fin15AnchoredAtom4188 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28992 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom4189 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2381 Fin15AnchoredAtom2385 Fin15AnchoredAtom2396
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2649 Fin15AnchoredAtom4189 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28993 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom4190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2381 Fin15AnchoredAtom2386 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2650 Fin15AnchoredAtom4190 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28994 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom4192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2382 Fin15AnchoredAtom2384 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2448 Fin15AnchoredAtom2652 Fin15AnchoredAtom4192 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 7, 12}, {0, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28995 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom4193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2382 Fin15AnchoredAtom2385 Fin15AnchoredAtom2400
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2653 Fin15AnchoredAtom4193 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28996 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom4194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2382 Fin15AnchoredAtom2386 Fin15AnchoredAtom2401
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2654 Fin15AnchoredAtom4194 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28997 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom4198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2384 Fin15AnchoredAtom2385 Fin15AnchoredAtom2405
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2658 Fin15AnchoredAtom4198 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 7, 13}, {0, 3, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28998 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom4199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2384 Fin15AnchoredAtom2386 Fin15AnchoredAtom2406
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2659 Fin15AnchoredAtom4199 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28999 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom4200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2385 Fin15AnchoredAtom2386 Fin15AnchoredAtom2407
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2660 Fin15AnchoredAtom4200 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 7, 14}, {0, 3, 5, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29000 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom4201 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2387 Fin15AnchoredAtom2388 Fin15AnchoredAtom2393
    Fin15AnchoredAtom2457 Fin15AnchoredAtom2661 Fin15AnchoredAtom4201 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 9, 10}, {0, 5, 8, 9, 10}, {0, 3, 8, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 5, 8, 10}, {0, 3, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29001 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom4203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2387 Fin15AnchoredAtom2390 Fin15AnchoredAtom2395
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2663 Fin15AnchoredAtom4203 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 9, 12}, {0, 5, 8, 9, 12}, {0, 3, 8, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29002 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom4205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2387 Fin15AnchoredAtom2392 Fin15AnchoredAtom2397
    Fin15AnchoredAtom2461 Fin15AnchoredAtom2665 Fin15AnchoredAtom4205 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 9, 14}, {0, 5, 8, 9, 14}, {0, 3, 8, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29003 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom4207 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2388 Fin15AnchoredAtom2390 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2463 Fin15AnchoredAtom2667 Fin15AnchoredAtom4207 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 10, 12}, {0, 5, 8, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 8, 12}, {0, 3, 5, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29004 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom4208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2388 Fin15AnchoredAtom2391 Fin15AnchoredAtom2400
    Fin15AnchoredAtom2464 Fin15AnchoredAtom2668 Fin15AnchoredAtom4208 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 10, 13}, {0, 5, 8, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 8, 13}, {0, 3, 5, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29005 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom4214 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2390 Fin15AnchoredAtom2392 Fin15AnchoredAtom2406
    Fin15AnchoredAtom2470 Fin15AnchoredAtom2674 Fin15AnchoredAtom4214 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 12, 14}, {0, 5, 8, 12, 14}, {0, 3, 8, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29006 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom4215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2391 Fin15AnchoredAtom2392 Fin15AnchoredAtom2407
    Fin15AnchoredAtom2471 Fin15AnchoredAtom2675 Fin15AnchoredAtom4215 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 13, 14}, {0, 5, 8, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 8, 14}, {0, 3, 5, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29007 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom4217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2393 Fin15AnchoredAtom2395 Fin15AnchoredAtom2399
    Fin15AnchoredAtom2473 Fin15AnchoredAtom2677 Fin15AnchoredAtom4217 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 5, 9, 12}, {0, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29008 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom4218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2393 Fin15AnchoredAtom2396 Fin15AnchoredAtom2400
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2678 Fin15AnchoredAtom4218 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29009 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom4219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2393 Fin15AnchoredAtom2397 Fin15AnchoredAtom2401
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2679 Fin15AnchoredAtom4219 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29010 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom4223 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2395 Fin15AnchoredAtom2396 Fin15AnchoredAtom2405
    Fin15AnchoredAtom2479 Fin15AnchoredAtom2683 Fin15AnchoredAtom4223 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 9, 13}, {0, 3, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29011 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom4224 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2395 Fin15AnchoredAtom2397 Fin15AnchoredAtom2406
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2684 Fin15AnchoredAtom4224 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29012 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom4225 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2396 Fin15AnchoredAtom2397 Fin15AnchoredAtom2407
    Fin15AnchoredAtom2481 Fin15AnchoredAtom2685 Fin15AnchoredAtom4225 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 9, 14}, {0, 3, 5, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29013 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom4229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2399 Fin15AnchoredAtom2400 Fin15AnchoredAtom2405
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2689 Fin15AnchoredAtom4229 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 5, 10, 13}, {0, 3, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29014 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom4230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2399 Fin15AnchoredAtom2401 Fin15AnchoredAtom2406
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2690 Fin15AnchoredAtom4230 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29015 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom4231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2400 Fin15AnchoredAtom2401 Fin15AnchoredAtom2407
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2691 Fin15AnchoredAtom4231 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 10, 14}, {0, 3, 5, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29016 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2403 chi ∧
      Fin15AnchoredAtom2404 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2490 chi ∧
      Fin15AnchoredAtom2694 chi ∧
      Fin15AnchoredAtom4234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2403 Fin15AnchoredAtom2404 Fin15AnchoredAtom2407
    Fin15AnchoredAtom2490 Fin15AnchoredAtom2694 Fin15AnchoredAtom4234 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 11, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 11, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 11, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 11, 13, 14}, {0, 5, 11, 13, 14}, {0, 3, 11, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 11, 14}, {0, 3, 5, 11, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29017 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom4235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2405 Fin15AnchoredAtom2406 Fin15AnchoredAtom2407
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2695 Fin15AnchoredAtom4235 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 5, 12, 14}, {0, 3, 5, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29018 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom4236 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2409 Fin15AnchoredAtom2415
    Fin15AnchoredAtom2436 Fin15AnchoredAtom2696 Fin15AnchoredAtom4236 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 8, 9}, {0, 6, 7, 8, 9}, {0, 3, 7, 8, 9}, {0, 3, 6, 8, 9}, {0, 3, 6, 7, 9}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29019 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom4240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2413 Fin15AnchoredAtom2419
    Fin15AnchoredAtom2440 Fin15AnchoredAtom2700 Fin15AnchoredAtom4240 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 8, 13}, {0, 6, 7, 8, 13}, {0, 3, 7, 8, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29020 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2701 chi ∧
      Fin15AnchoredAtom4241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2408 Fin15AnchoredAtom2414 Fin15AnchoredAtom2420
    Fin15AnchoredAtom2441 Fin15AnchoredAtom2701 Fin15AnchoredAtom4241 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 8, 14}, {0, 6, 7, 8, 14}, {0, 3, 7, 8, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29021 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom4242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2409 Fin15AnchoredAtom2410 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2442 Fin15AnchoredAtom2702 Fin15AnchoredAtom4242 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 10}, {0, 6, 7, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 6, 7, 10}, {0, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29022 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom4244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2409 Fin15AnchoredAtom2412 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2444 Fin15AnchoredAtom2704 Fin15AnchoredAtom4244 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 12}, {0, 6, 7, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29023 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom4245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2409 Fin15AnchoredAtom2413 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2445 Fin15AnchoredAtom2705 Fin15AnchoredAtom4245 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 13}, {0, 6, 7, 9, 13}, {0, 3, 7, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29024 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom4246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2409 Fin15AnchoredAtom2414 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2446 Fin15AnchoredAtom2706 Fin15AnchoredAtom4246 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 14}, {0, 6, 7, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29025 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom4248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2410 Fin15AnchoredAtom2412 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2448 Fin15AnchoredAtom2708 Fin15AnchoredAtom4248 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 12}, {0, 6, 7, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 7, 12}, {0, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29026 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom4249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2410 Fin15AnchoredAtom2413 Fin15AnchoredAtom2428
    Fin15AnchoredAtom2449 Fin15AnchoredAtom2709 Fin15AnchoredAtom4249 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 13}, {0, 6, 7, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29027 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom4250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2410 Fin15AnchoredAtom2414 Fin15AnchoredAtom2429
    Fin15AnchoredAtom2450 Fin15AnchoredAtom2710 Fin15AnchoredAtom4250 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 14}, {0, 6, 7, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29028 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom4254 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2412 Fin15AnchoredAtom2413 Fin15AnchoredAtom2433
    Fin15AnchoredAtom2454 Fin15AnchoredAtom2714 Fin15AnchoredAtom4254 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 12, 13}, {0, 6, 7, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 7, 13}, {0, 3, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29029 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom4255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2412 Fin15AnchoredAtom2414 Fin15AnchoredAtom2434
    Fin15AnchoredAtom2455 Fin15AnchoredAtom2715 Fin15AnchoredAtom4255 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 12, 14}, {0, 6, 7, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29030 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom4256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2413 Fin15AnchoredAtom2414 Fin15AnchoredAtom2435
    Fin15AnchoredAtom2456 Fin15AnchoredAtom2716 Fin15AnchoredAtom4256 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 13, 14}, {0, 6, 7, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 7, 14}, {0, 3, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29031 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom4257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2415 Fin15AnchoredAtom2416 Fin15AnchoredAtom2421
    Fin15AnchoredAtom2457 Fin15AnchoredAtom2717 Fin15AnchoredAtom4257 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 9, 10}, {0, 6, 8, 9, 10}, {0, 3, 8, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 6, 8, 10}, {0, 3, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29032 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom4259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2415 Fin15AnchoredAtom2418 Fin15AnchoredAtom2423
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2719 Fin15AnchoredAtom4259 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 9, 12}, {0, 6, 8, 9, 12}, {0, 3, 8, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29033 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom4260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2415 Fin15AnchoredAtom2419 Fin15AnchoredAtom2424
    Fin15AnchoredAtom2460 Fin15AnchoredAtom2720 Fin15AnchoredAtom4260 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 9, 13}, {0, 6, 8, 9, 13}, {0, 3, 8, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29034 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom4261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2415 Fin15AnchoredAtom2420 Fin15AnchoredAtom2425
    Fin15AnchoredAtom2461 Fin15AnchoredAtom2721 Fin15AnchoredAtom4261 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 9, 14}, {0, 6, 8, 9, 14}, {0, 3, 8, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29035 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom4263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2416 Fin15AnchoredAtom2418 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2463 Fin15AnchoredAtom2723 Fin15AnchoredAtom4263 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 10, 12}, {0, 6, 8, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 8, 12}, {0, 3, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29036 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom4265 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2416 Fin15AnchoredAtom2420 Fin15AnchoredAtom2429
    Fin15AnchoredAtom2465 Fin15AnchoredAtom2725 Fin15AnchoredAtom4265 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 10, 14}, {0, 6, 8, 10, 14}, {0, 3, 8, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29037 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom4269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2418 Fin15AnchoredAtom2419 Fin15AnchoredAtom2433
    Fin15AnchoredAtom2469 Fin15AnchoredAtom2729 Fin15AnchoredAtom4269 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 12, 13}, {0, 6, 8, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 8, 13}, {0, 3, 6, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29038 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom4270 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2418 Fin15AnchoredAtom2420 Fin15AnchoredAtom2434
    Fin15AnchoredAtom2470 Fin15AnchoredAtom2730 Fin15AnchoredAtom4270 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 12, 14}, {0, 6, 8, 12, 14}, {0, 3, 8, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29039 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom4271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2419 Fin15AnchoredAtom2420 Fin15AnchoredAtom2435
    Fin15AnchoredAtom2471 Fin15AnchoredAtom2731 Fin15AnchoredAtom4271 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 13, 14}, {0, 6, 8, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 8, 14}, {0, 3, 6, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29040 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom4273 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2421 Fin15AnchoredAtom2423 Fin15AnchoredAtom2427
    Fin15AnchoredAtom2473 Fin15AnchoredAtom2733 Fin15AnchoredAtom4273 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 6, 9, 12}, {0, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29041 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom4274 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2421 Fin15AnchoredAtom2424 Fin15AnchoredAtom2428
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2734 Fin15AnchoredAtom4274 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29042 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom4275 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2421 Fin15AnchoredAtom2425 Fin15AnchoredAtom2429
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2735 Fin15AnchoredAtom4275 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29043 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom4279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2423 Fin15AnchoredAtom2424 Fin15AnchoredAtom2433
    Fin15AnchoredAtom2479 Fin15AnchoredAtom2739 Fin15AnchoredAtom4279 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 9, 13}, {0, 3, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29044 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom4280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2423 Fin15AnchoredAtom2425 Fin15AnchoredAtom2434
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2740 Fin15AnchoredAtom4280 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29045 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom4281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2424 Fin15AnchoredAtom2425 Fin15AnchoredAtom2435
    Fin15AnchoredAtom2481 Fin15AnchoredAtom2741 Fin15AnchoredAtom4281 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 9, 14}, {0, 3, 6, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29046 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom4285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2427 Fin15AnchoredAtom2428 Fin15AnchoredAtom2433
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2745 Fin15AnchoredAtom4285 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 6, 12, 13}, {0, 3, 6, 10, 13}, {0, 3, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29047 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom4286 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2427 Fin15AnchoredAtom2429 Fin15AnchoredAtom2434
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2746 Fin15AnchoredAtom4286 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29048 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom4287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2428 Fin15AnchoredAtom2429 Fin15AnchoredAtom2435
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2747 Fin15AnchoredAtom4287 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 10, 14}, {0, 3, 6, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29049 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom4291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2433 Fin15AnchoredAtom2434 Fin15AnchoredAtom2435
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2751 Fin15AnchoredAtom4291 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 6, 13, 14}, {0, 3, 6, 12, 14}, {0, 3, 6, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29050 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2752 chi ∧
      Fin15AnchoredAtom4292 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2436 Fin15AnchoredAtom2437 Fin15AnchoredAtom2442
    Fin15AnchoredAtom2457 Fin15AnchoredAtom2752 Fin15AnchoredAtom4292 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 9, 10}, {0, 7, 8, 9, 10}, {0, 3, 8, 9, 10}, {0, 3, 7, 9, 10}, {0, 3, 7, 8, 10}, {0, 3, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29051 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom4294 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2436 Fin15AnchoredAtom2439 Fin15AnchoredAtom2444
    Fin15AnchoredAtom2459 Fin15AnchoredAtom2754 Fin15AnchoredAtom4294 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 9, 12}, {0, 7, 8, 9, 12}, {0, 3, 8, 9, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29052 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2436 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2756 chi ∧
      Fin15AnchoredAtom4296 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2436 Fin15AnchoredAtom2441 Fin15AnchoredAtom2446
    Fin15AnchoredAtom2461 Fin15AnchoredAtom2756 Fin15AnchoredAtom4296 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 9, 14}, {0, 7, 8, 9, 14}, {0, 3, 8, 9, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29053 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2758 chi ∧
      Fin15AnchoredAtom4298 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2437 Fin15AnchoredAtom2439 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2463 Fin15AnchoredAtom2758 Fin15AnchoredAtom4298 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 10, 12}, {0, 7, 8, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 8, 12}, {0, 3, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29054 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2759 chi ∧
      Fin15AnchoredAtom4299 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2437 Fin15AnchoredAtom2440 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2464 Fin15AnchoredAtom2759 Fin15AnchoredAtom4299 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 10, 13}, {0, 7, 8, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29055 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2760 chi ∧
      Fin15AnchoredAtom4300 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2437 Fin15AnchoredAtom2441 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2465 Fin15AnchoredAtom2760 Fin15AnchoredAtom4300 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 10, 14}, {0, 7, 8, 10, 14}, {0, 3, 8, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
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
