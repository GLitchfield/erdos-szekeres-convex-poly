module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 227. -/

theorem fin15Anchored_clause29056 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2764 chi ∧
      Fin15AnchoredAtom4304 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2439 Fin15AnchoredAtom2440 Fin15AnchoredAtom2454
    Fin15AnchoredAtom2469 Fin15AnchoredAtom2764 Fin15AnchoredAtom4304 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 12, 13}, {0, 7, 8, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 8, 13}, {0, 3, 7, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29057 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2439 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2765 chi ∧
      Fin15AnchoredAtom4305 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2439 Fin15AnchoredAtom2441 Fin15AnchoredAtom2455
    Fin15AnchoredAtom2470 Fin15AnchoredAtom2765 Fin15AnchoredAtom4305 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 12, 14}, {0, 7, 8, 12, 14}, {0, 3, 8, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29058 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2440 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2766 chi ∧
      Fin15AnchoredAtom4306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2440 Fin15AnchoredAtom2441 Fin15AnchoredAtom2456
    Fin15AnchoredAtom2471 Fin15AnchoredAtom2766 Fin15AnchoredAtom4306 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 13, 14}, {0, 7, 8, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 8, 14}, {0, 3, 7, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29059 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom4308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2442 Fin15AnchoredAtom2444 Fin15AnchoredAtom2448
    Fin15AnchoredAtom2473 Fin15AnchoredAtom2768 Fin15AnchoredAtom4308 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 3, 7, 10, 12}, {0, 3, 7, 9, 12}, {0, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29060 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom4309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2442 Fin15AnchoredAtom2445 Fin15AnchoredAtom2449
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2769 Fin15AnchoredAtom4309 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29061 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom4310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2442 Fin15AnchoredAtom2446 Fin15AnchoredAtom2450
    Fin15AnchoredAtom2475 Fin15AnchoredAtom2770 Fin15AnchoredAtom4310 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29062 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom4314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2444 Fin15AnchoredAtom2445 Fin15AnchoredAtom2454
    Fin15AnchoredAtom2479 Fin15AnchoredAtom2774 Fin15AnchoredAtom4314 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 9, 13}, {0, 3, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29063 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom4315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2444 Fin15AnchoredAtom2446 Fin15AnchoredAtom2455
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2775 Fin15AnchoredAtom4315 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29064 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom4316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2445 Fin15AnchoredAtom2446 Fin15AnchoredAtom2456
    Fin15AnchoredAtom2481 Fin15AnchoredAtom2776 Fin15AnchoredAtom4316 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 13, 14}, {0, 7, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 9, 14}, {0, 3, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29065 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom4320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2448 Fin15AnchoredAtom2449 Fin15AnchoredAtom2454
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2780 Fin15AnchoredAtom4320 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 7, 12, 13}, {0, 3, 7, 10, 13}, {0, 3, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29066 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom4321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2448 Fin15AnchoredAtom2450 Fin15AnchoredAtom2455
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2781 Fin15AnchoredAtom4321 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29067 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom4322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2449 Fin15AnchoredAtom2450 Fin15AnchoredAtom2456
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2782 Fin15AnchoredAtom4322 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 10, 14}, {0, 3, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29068 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom4326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2454 Fin15AnchoredAtom2455 Fin15AnchoredAtom2456
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2786 Fin15AnchoredAtom4326 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 7, 13, 14}, {0, 3, 7, 12, 14}, {0, 3, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29069 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2788 chi ∧
      Fin15AnchoredAtom4328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2457 Fin15AnchoredAtom2459 Fin15AnchoredAtom2463
    Fin15AnchoredAtom2473 Fin15AnchoredAtom2788 Fin15AnchoredAtom4328 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 8, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 8, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 9, 10, 12}, {0, 8, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 3, 8, 10, 12}, {0, 3, 8, 9, 12}, {0, 3, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29070 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2789 chi ∧
      Fin15AnchoredAtom4329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2457 Fin15AnchoredAtom2460 Fin15AnchoredAtom2464
    Fin15AnchoredAtom2474 Fin15AnchoredAtom2789 Fin15AnchoredAtom4329 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 9, 10, 13}, {0, 8, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29071 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2794 chi ∧
      Fin15AnchoredAtom4334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2459 Fin15AnchoredAtom2460 Fin15AnchoredAtom2469
    Fin15AnchoredAtom2479 Fin15AnchoredAtom2794 Fin15AnchoredAtom4334 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 9, 12, 13}, {0, 8, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 9, 13}, {0, 3, 8, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29072 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2795 chi ∧
      Fin15AnchoredAtom4335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2459 Fin15AnchoredAtom2461 Fin15AnchoredAtom2470
    Fin15AnchoredAtom2480 Fin15AnchoredAtom2795 Fin15AnchoredAtom4335 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 8, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 9, 12, 14}, {0, 8, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 8, 12, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29073 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2796 chi ∧
      Fin15AnchoredAtom4336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2460 Fin15AnchoredAtom2461 Fin15AnchoredAtom2471
    Fin15AnchoredAtom2481 Fin15AnchoredAtom2796 Fin15AnchoredAtom4336 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 9, 13, 14}, {0, 8, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 9, 14}, {0, 3, 8, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29074 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2800 chi ∧
      Fin15AnchoredAtom4340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2463 Fin15AnchoredAtom2464 Fin15AnchoredAtom2469
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2800 Fin15AnchoredAtom4340 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 10, 12, 13}, {0, 8, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 8, 12, 13}, {0, 3, 8, 10, 13}, {0, 3, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29075 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2801 chi ∧
      Fin15AnchoredAtom4341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2463 Fin15AnchoredAtom2465 Fin15AnchoredAtom2470
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2801 Fin15AnchoredAtom4341 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 10, 12, 14}, {0, 8, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 8, 12, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29076 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2802 chi ∧
      Fin15AnchoredAtom4342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2464 Fin15AnchoredAtom2465 Fin15AnchoredAtom2471
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2802 Fin15AnchoredAtom4342 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 10, 13, 14}, {0, 8, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 10, 14}, {0, 3, 8, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29077 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2806 chi ∧
      Fin15AnchoredAtom4346 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2469 Fin15AnchoredAtom2470 Fin15AnchoredAtom2471
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2806 Fin15AnchoredAtom4346 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 8, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 8, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 12, 13, 14}, {0, 8, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 8, 13, 14}, {0, 3, 8, 12, 14}, {0, 3, 8, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29078 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2473 Fin15AnchoredAtom2474 Fin15AnchoredAtom2479
    Fin15AnchoredAtom2485 Fin15AnchoredAtom2810 Fin15AnchoredAtom4350 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 12, 13}, {0, 9, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 9, 12, 13}, {0, 3, 9, 10, 13}, {0, 3, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29079 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2473 Fin15AnchoredAtom2475 Fin15AnchoredAtom2480
    Fin15AnchoredAtom2486 Fin15AnchoredAtom2811 Fin15AnchoredAtom4351 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 12, 14}, {0, 9, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29080 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4352 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2474 Fin15AnchoredAtom2475 Fin15AnchoredAtom2481
    Fin15AnchoredAtom2487 Fin15AnchoredAtom2812 Fin15AnchoredAtom4352 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 13, 14}, {0, 9, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 10, 14}, {0, 3, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29081 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2479 Fin15AnchoredAtom2480 Fin15AnchoredAtom2481
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2816 Fin15AnchoredAtom4356 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 9, 13, 14}, {0, 3, 9, 12, 14}, {0, 3, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29082 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2482 chi ∧
      Fin15AnchoredAtom2483 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2488 chi ∧
      Fin15AnchoredAtom2817 chi ∧
      Fin15AnchoredAtom4357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2482 Fin15AnchoredAtom2483 Fin15AnchoredAtom2485
    Fin15AnchoredAtom2488 Fin15AnchoredAtom2817 Fin15AnchoredAtom4357 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 10, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 10, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 10, 11, 12, 13}, {0, 10, 11, 12, 13}, {0, 3, 11, 12, 13}, {0, 3, 10, 12, 13}, {0, 3, 10, 11, 13}, {0, 3, 10, 11, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29083 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2485 Fin15AnchoredAtom2486 Fin15AnchoredAtom2487
    Fin15AnchoredAtom2491 Fin15AnchoredAtom2820 Fin15AnchoredAtom4360 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 10, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 3, 10, 13, 14}, {0, 3, 10, 12, 14}, {0, 3, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29084 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2612 chi ∧
      Fin15AnchoredAtom4362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2493 Fin15AnchoredAtom2500
    Fin15AnchoredAtom2528 Fin15AnchoredAtom2612 Fin15AnchoredAtom4362 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 8}, {0, 5, 6, 7, 8}, {0, 4, 6, 7, 8}, {0, 4, 5, 7, 8}, {0, 4, 5, 6, 8}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29085 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom4363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2494 Fin15AnchoredAtom2501
    Fin15AnchoredAtom2529 Fin15AnchoredAtom2613 Fin15AnchoredAtom4363 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 9}, {0, 5, 6, 7, 9}, {0, 4, 6, 7, 9}, {0, 4, 5, 7, 9}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29086 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom4364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2495 Fin15AnchoredAtom2502
    Fin15AnchoredAtom2530 Fin15AnchoredAtom2614 Fin15AnchoredAtom4364 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 10}, {0, 5, 6, 7, 10}, {0, 4, 6, 7, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29087 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom2503 chi ∧
      Fin15AnchoredAtom2531 chi ∧
      Fin15AnchoredAtom2615 chi ∧
      Fin15AnchoredAtom4365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2496 Fin15AnchoredAtom2503
    Fin15AnchoredAtom2531 Fin15AnchoredAtom2615 Fin15AnchoredAtom4365 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 7, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 7, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 7, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 11}, {0, 5, 6, 7, 11}, {0, 4, 6, 7, 11}, {0, 4, 5, 7, 11}, {0, 4, 5, 6, 11}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29088 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom4366 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2497 Fin15AnchoredAtom2504
    Fin15AnchoredAtom2532 Fin15AnchoredAtom2616 Fin15AnchoredAtom4366 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 12}, {0, 5, 6, 7, 12}, {0, 4, 6, 7, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29089 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom4367 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2498 Fin15AnchoredAtom2505
    Fin15AnchoredAtom2533 Fin15AnchoredAtom2617 Fin15AnchoredAtom4367 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 13}, {0, 5, 6, 7, 13}, {0, 4, 6, 7, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29090 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom4368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2492 Fin15AnchoredAtom2499 Fin15AnchoredAtom2506
    Fin15AnchoredAtom2534 Fin15AnchoredAtom2618 Fin15AnchoredAtom4368 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 14}, {0, 5, 6, 7, 14}, {0, 4, 6, 7, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29091 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom4369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2494 Fin15AnchoredAtom2507
    Fin15AnchoredAtom2535 Fin15AnchoredAtom2619 Fin15AnchoredAtom4369 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 9}, {0, 5, 6, 8, 9}, {0, 4, 6, 8, 9}, {0, 4, 5, 8, 9}, {0, 4, 5, 6, 9}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29092 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2620 chi ∧
      Fin15AnchoredAtom4370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2495 Fin15AnchoredAtom2508
    Fin15AnchoredAtom2536 Fin15AnchoredAtom2620 Fin15AnchoredAtom4370 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 10}, {0, 5, 6, 8, 10}, {0, 4, 6, 8, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29093 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2622 chi ∧
      Fin15AnchoredAtom4372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2497 Fin15AnchoredAtom2510
    Fin15AnchoredAtom2538 Fin15AnchoredAtom2622 Fin15AnchoredAtom4372 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 12}, {0, 5, 6, 8, 12}, {0, 4, 6, 8, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29094 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2511 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2623 chi ∧
      Fin15AnchoredAtom4373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2498 Fin15AnchoredAtom2511
    Fin15AnchoredAtom2539 Fin15AnchoredAtom2623 Fin15AnchoredAtom4373 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 13}, {0, 5, 6, 8, 13}, {0, 4, 6, 8, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29095 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom4374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2493 Fin15AnchoredAtom2499 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2540 Fin15AnchoredAtom2624 Fin15AnchoredAtom4374 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 14}, {0, 5, 6, 8, 14}, {0, 4, 6, 8, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29096 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom4375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2494 Fin15AnchoredAtom2495 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2541 Fin15AnchoredAtom2625 Fin15AnchoredAtom4375 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 10}, {0, 5, 6, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 6, 10}, {0, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29097 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2542 chi ∧
      Fin15AnchoredAtom2626 chi ∧
      Fin15AnchoredAtom4376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2494 Fin15AnchoredAtom2496 Fin15AnchoredAtom2514
    Fin15AnchoredAtom2542 Fin15AnchoredAtom2626 Fin15AnchoredAtom4376 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 9, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 9, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 9, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 11}, {0, 5, 6, 9, 11}, {0, 4, 6, 9, 11}, {0, 4, 5, 9, 11}, {0, 4, 5, 6, 11}, {0, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29098 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom4377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2494 Fin15AnchoredAtom2497 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2543 Fin15AnchoredAtom2627 Fin15AnchoredAtom4377 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 12}, {0, 5, 6, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29099 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom4378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2494 Fin15AnchoredAtom2498 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2544 Fin15AnchoredAtom2628 Fin15AnchoredAtom4378 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 13}, {0, 5, 6, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29100 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom4379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2494 Fin15AnchoredAtom2499 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2545 Fin15AnchoredAtom2629 Fin15AnchoredAtom4379 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 14}, {0, 5, 6, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29101 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2546 chi ∧
      Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom4380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2495 Fin15AnchoredAtom2496 Fin15AnchoredAtom2518
    Fin15AnchoredAtom2546 Fin15AnchoredAtom2630 Fin15AnchoredAtom4380 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 11}, {0, 5, 6, 10, 11}, {0, 4, 6, 10, 11}, {0, 4, 5, 10, 11}, {0, 4, 5, 6, 11}, {0, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29102 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom4381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2495 Fin15AnchoredAtom2497 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2547 Fin15AnchoredAtom2631 Fin15AnchoredAtom4381 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 12}, {0, 5, 6, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 6, 12}, {0, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29103 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom4382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2495 Fin15AnchoredAtom2498 Fin15AnchoredAtom2520
    Fin15AnchoredAtom2548 Fin15AnchoredAtom2632 Fin15AnchoredAtom4382 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 13}, {0, 5, 6, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29104 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom4383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2495 Fin15AnchoredAtom2499 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2549 Fin15AnchoredAtom2633 Fin15AnchoredAtom4383 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 14}, {0, 5, 6, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29105 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom4387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2497 Fin15AnchoredAtom2498 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2553 Fin15AnchoredAtom2637 Fin15AnchoredAtom4387 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 13}, {0, 5, 6, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 6, 13}, {0, 4, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29106 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom4388 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2497 Fin15AnchoredAtom2499 Fin15AnchoredAtom2526
    Fin15AnchoredAtom2554 Fin15AnchoredAtom2638 Fin15AnchoredAtom4388 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 14}, {0, 5, 6, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29107 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom4389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2498 Fin15AnchoredAtom2499 Fin15AnchoredAtom2527
    Fin15AnchoredAtom2555 Fin15AnchoredAtom2639 Fin15AnchoredAtom4389 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 13, 14}, {0, 5, 6, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 6, 14}, {0, 4, 5, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29108 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom4390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2501 Fin15AnchoredAtom2507
    Fin15AnchoredAtom2556 Fin15AnchoredAtom2640 Fin15AnchoredAtom4390 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 9}, {0, 5, 7, 8, 9}, {0, 4, 7, 8, 9}, {0, 4, 5, 8, 9}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29109 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom2641 chi ∧
      Fin15AnchoredAtom4391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2502 Fin15AnchoredAtom2508
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2641 Fin15AnchoredAtom4391 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 10}, {0, 5, 7, 8, 10}, {0, 4, 7, 8, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29110 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom4395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2500 Fin15AnchoredAtom2506 Fin15AnchoredAtom2512
    Fin15AnchoredAtom2561 Fin15AnchoredAtom2645 Fin15AnchoredAtom4395 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 8, 14}, {0, 5, 7, 8, 14}, {0, 4, 7, 8, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29111 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom4396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2501 Fin15AnchoredAtom2502 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2562 Fin15AnchoredAtom2646 Fin15AnchoredAtom4396 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 7, 10}, {0, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29112 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom4398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2501 Fin15AnchoredAtom2504 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2648 Fin15AnchoredAtom4398 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29113 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom4399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2501 Fin15AnchoredAtom2505 Fin15AnchoredAtom2516
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2649 Fin15AnchoredAtom4399 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29114 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom4400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2501 Fin15AnchoredAtom2506 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2650 Fin15AnchoredAtom4400 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29115 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2503 chi ∧
      Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2567 chi ∧
      Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom4401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2502 Fin15AnchoredAtom2503 Fin15AnchoredAtom2518
    Fin15AnchoredAtom2567 Fin15AnchoredAtom2651 Fin15AnchoredAtom4401 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 11}, {0, 5, 7, 10, 11}, {0, 4, 7, 10, 11}, {0, 4, 5, 10, 11}, {0, 4, 5, 7, 11}, {0, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29116 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom4402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2502 Fin15AnchoredAtom2504 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2568 Fin15AnchoredAtom2652 Fin15AnchoredAtom4402 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 7, 12}, {0, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29117 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom4403 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2502 Fin15AnchoredAtom2505 Fin15AnchoredAtom2520
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2653 Fin15AnchoredAtom4403 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29118 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom4404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2502 Fin15AnchoredAtom2506 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2654 Fin15AnchoredAtom4404 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29119 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom4408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2504 Fin15AnchoredAtom2505 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2658 Fin15AnchoredAtom4408 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 7, 13}, {0, 4, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29120 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom4409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2504 Fin15AnchoredAtom2506 Fin15AnchoredAtom2526
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2659 Fin15AnchoredAtom4409 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29121 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom4410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2505 Fin15AnchoredAtom2506 Fin15AnchoredAtom2527
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2660 Fin15AnchoredAtom4410 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 7, 14}, {0, 4, 5, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29122 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom4411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2507 Fin15AnchoredAtom2508 Fin15AnchoredAtom2513
    Fin15AnchoredAtom2577 Fin15AnchoredAtom2661 Fin15AnchoredAtom4411 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 10}, {0, 5, 8, 9, 10}, {0, 4, 8, 9, 10}, {0, 4, 5, 9, 10}, {0, 4, 5, 8, 10}, {0, 4, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29123 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom4413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2507 Fin15AnchoredAtom2510 Fin15AnchoredAtom2515
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2663 Fin15AnchoredAtom4413 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 12}, {0, 5, 8, 9, 12}, {0, 4, 8, 9, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29124 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom4415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2507 Fin15AnchoredAtom2512 Fin15AnchoredAtom2517
    Fin15AnchoredAtom2581 Fin15AnchoredAtom2665 Fin15AnchoredAtom4415 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 14}, {0, 5, 8, 9, 14}, {0, 4, 8, 9, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29125 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom4417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2508 Fin15AnchoredAtom2510 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2583 Fin15AnchoredAtom2667 Fin15AnchoredAtom4417 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 10, 12}, {0, 5, 8, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 8, 12}, {0, 4, 5, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29126 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom2669 chi ∧
      Fin15AnchoredAtom4419 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2508 Fin15AnchoredAtom2512 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2585 Fin15AnchoredAtom2669 Fin15AnchoredAtom4419 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 10, 14}, {0, 5, 8, 10, 14}, {0, 4, 8, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29127 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2511 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom4423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2510 Fin15AnchoredAtom2511 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2589 Fin15AnchoredAtom2673 Fin15AnchoredAtom4423 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 12, 13}, {0, 5, 8, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 8, 13}, {0, 4, 5, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29128 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom4424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2510 Fin15AnchoredAtom2512 Fin15AnchoredAtom2526
    Fin15AnchoredAtom2590 Fin15AnchoredAtom2674 Fin15AnchoredAtom4424 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 12, 14}, {0, 5, 8, 12, 14}, {0, 4, 8, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 8, 14}, {0, 4, 5, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29129 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2592 chi ∧
      Fin15AnchoredAtom2676 chi ∧
      Fin15AnchoredAtom4426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2513 Fin15AnchoredAtom2514 Fin15AnchoredAtom2518
    Fin15AnchoredAtom2592 Fin15AnchoredAtom2676 Fin15AnchoredAtom4426 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 11}, {0, 5, 9, 10, 11}, {0, 4, 9, 10, 11}, {0, 4, 5, 10, 11}, {0, 4, 5, 9, 11}, {0, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29130 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom4427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2513 Fin15AnchoredAtom2515 Fin15AnchoredAtom2519
    Fin15AnchoredAtom2593 Fin15AnchoredAtom2677 Fin15AnchoredAtom4427 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29131 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom4428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2513 Fin15AnchoredAtom2516 Fin15AnchoredAtom2520
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2678 Fin15AnchoredAtom4428 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29132 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom4429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2513 Fin15AnchoredAtom2517 Fin15AnchoredAtom2521
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2679 Fin15AnchoredAtom4429 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29133 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2522 chi ∧
      Fin15AnchoredAtom2596 chi ∧
      Fin15AnchoredAtom2680 chi ∧
      Fin15AnchoredAtom4430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2514 Fin15AnchoredAtom2515 Fin15AnchoredAtom2522
    Fin15AnchoredAtom2596 Fin15AnchoredAtom2680 Fin15AnchoredAtom4430 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 11, 12}, {0, 5, 9, 11, 12}, {0, 4, 9, 11, 12}, {0, 4, 5, 11, 12}, {0, 4, 5, 9, 12}, {0, 4, 5, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29134 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2523 chi ∧
      Fin15AnchoredAtom2597 chi ∧
      Fin15AnchoredAtom2681 chi ∧
      Fin15AnchoredAtom4431 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2514 Fin15AnchoredAtom2516 Fin15AnchoredAtom2523
    Fin15AnchoredAtom2597 Fin15AnchoredAtom2681 Fin15AnchoredAtom4431 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 11, 13}, {0, 5, 9, 11, 13}, {0, 4, 9, 11, 13}, {0, 4, 5, 11, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29135 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2524 chi ∧
      Fin15AnchoredAtom2598 chi ∧
      Fin15AnchoredAtom2682 chi ∧
      Fin15AnchoredAtom4432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2514 Fin15AnchoredAtom2517 Fin15AnchoredAtom2524
    Fin15AnchoredAtom2598 Fin15AnchoredAtom2682 Fin15AnchoredAtom4432 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 11, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 11, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 11, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 11, 14}, {0, 5, 9, 11, 14}, {0, 4, 9, 11, 14}, {0, 4, 5, 11, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29136 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom4433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2515 Fin15AnchoredAtom2516 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2599 Fin15AnchoredAtom2683 Fin15AnchoredAtom4433 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 9, 13}, {0, 4, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29137 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom4434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2515 Fin15AnchoredAtom2517 Fin15AnchoredAtom2526
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2684 Fin15AnchoredAtom4434 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29138 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom4435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2516 Fin15AnchoredAtom2517 Fin15AnchoredAtom2527
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2685 Fin15AnchoredAtom4435 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 9, 14}, {0, 4, 5, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29139 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2522 chi ∧
      Fin15AnchoredAtom2602 chi ∧
      Fin15AnchoredAtom2686 chi ∧
      Fin15AnchoredAtom4436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2518 Fin15AnchoredAtom2519 Fin15AnchoredAtom2522
    Fin15AnchoredAtom2602 Fin15AnchoredAtom2686 Fin15AnchoredAtom4436 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 11, 12}, {0, 5, 10, 11, 12}, {0, 4, 10, 11, 12}, {0, 4, 5, 11, 12}, {0, 4, 5, 10, 12}, {0, 4, 5, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29140 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2523 chi ∧
      Fin15AnchoredAtom2603 chi ∧
      Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom4437 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2518 Fin15AnchoredAtom2520 Fin15AnchoredAtom2523
    Fin15AnchoredAtom2603 Fin15AnchoredAtom2687 Fin15AnchoredAtom4437 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 10, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 11, 13}, {0, 5, 10, 11, 13}, {0, 4, 10, 11, 13}, {0, 4, 5, 11, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29141 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom4439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2519 Fin15AnchoredAtom2520 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2689 Fin15AnchoredAtom4439 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 10, 13}, {0, 4, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29142 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom4440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2519 Fin15AnchoredAtom2521 Fin15AnchoredAtom2526
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2690 Fin15AnchoredAtom4440 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29143 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom4441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2520 Fin15AnchoredAtom2521 Fin15AnchoredAtom2527
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2691 Fin15AnchoredAtom4441 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 10, 14}, {0, 4, 5, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29144 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2522 chi ∧
      Fin15AnchoredAtom2523 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2608 chi ∧
      Fin15AnchoredAtom2692 chi ∧
      Fin15AnchoredAtom4442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2522 Fin15AnchoredAtom2523 Fin15AnchoredAtom2525
    Fin15AnchoredAtom2608 Fin15AnchoredAtom2692 Fin15AnchoredAtom4442 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 11, 12, 13}, {0, 5, 11, 12, 13}, {0, 4, 11, 12, 13}, {0, 4, 5, 12, 13}, {0, 4, 5, 11, 13}, {0, 4, 5, 11, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29145 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom4445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2525 Fin15AnchoredAtom2526 Fin15AnchoredAtom2527
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2695 Fin15AnchoredAtom4445 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 5, 13, 14}, {0, 4, 5, 12, 14}, {0, 4, 5, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29146 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom2696 chi ∧
      Fin15AnchoredAtom4446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2529 Fin15AnchoredAtom2535
    Fin15AnchoredAtom2556 Fin15AnchoredAtom2696 Fin15AnchoredAtom4446 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 9}, {0, 6, 7, 8, 9}, {0, 4, 7, 8, 9}, {0, 4, 6, 8, 9}, {0, 4, 6, 7, 9}, {0, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29147 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom2697 chi ∧
      Fin15AnchoredAtom4447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2530 Fin15AnchoredAtom2536
    Fin15AnchoredAtom2557 Fin15AnchoredAtom2697 Fin15AnchoredAtom4447 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 10}, {0, 6, 7, 8, 10}, {0, 4, 7, 8, 10}, {0, 4, 6, 8, 10}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29148 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom2699 chi ∧
      Fin15AnchoredAtom4449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2532 Fin15AnchoredAtom2538
    Fin15AnchoredAtom2559 Fin15AnchoredAtom2699 Fin15AnchoredAtom4449 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 12}, {0, 6, 7, 8, 12}, {0, 4, 7, 8, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29149 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom2700 chi ∧
      Fin15AnchoredAtom4450 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2528 Fin15AnchoredAtom2533 Fin15AnchoredAtom2539
    Fin15AnchoredAtom2560 Fin15AnchoredAtom2700 Fin15AnchoredAtom4450 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 13}, {0, 6, 7, 8, 13}, {0, 4, 7, 8, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29150 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom4452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2530 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2562 Fin15AnchoredAtom2702 Fin15AnchoredAtom4452 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 10}, {0, 6, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 6, 7, 10}, {0, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29151 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2531 chi ∧
      Fin15AnchoredAtom2542 chi ∧
      Fin15AnchoredAtom2563 chi ∧
      Fin15AnchoredAtom2703 chi ∧
      Fin15AnchoredAtom4453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2531 Fin15AnchoredAtom2542
    Fin15AnchoredAtom2563 Fin15AnchoredAtom2703 Fin15AnchoredAtom4453 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 9, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 11}, {0, 6, 7, 9, 11}, {0, 4, 7, 9, 11}, {0, 4, 6, 9, 11}, {0, 4, 6, 7, 11}, {0, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29152 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom4454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2532 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2564 Fin15AnchoredAtom2704 Fin15AnchoredAtom4454 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 12}, {0, 6, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29153 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom4455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2533 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2565 Fin15AnchoredAtom2705 Fin15AnchoredAtom4455 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 13}, {0, 6, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29154 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom4456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2529 Fin15AnchoredAtom2534 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2566 Fin15AnchoredAtom2706 Fin15AnchoredAtom4456 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 14}, {0, 6, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29155 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom4458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2530 Fin15AnchoredAtom2532 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2568 Fin15AnchoredAtom2708 Fin15AnchoredAtom4458 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 12}, {0, 6, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 7, 12}, {0, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29156 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom4459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2530 Fin15AnchoredAtom2533 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2569 Fin15AnchoredAtom2709 Fin15AnchoredAtom4459 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 13}, {0, 6, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29157 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom4460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2530 Fin15AnchoredAtom2534 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2570 Fin15AnchoredAtom2710 Fin15AnchoredAtom4460 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 14}, {0, 6, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29158 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom4464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2532 Fin15AnchoredAtom2533 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2574 Fin15AnchoredAtom2714 Fin15AnchoredAtom4464 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 13}, {0, 6, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 7, 13}, {0, 4, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29159 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom4465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2532 Fin15AnchoredAtom2534 Fin15AnchoredAtom2554
    Fin15AnchoredAtom2575 Fin15AnchoredAtom2715 Fin15AnchoredAtom4465 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 14}, {0, 6, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29160 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom4466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2533 Fin15AnchoredAtom2534 Fin15AnchoredAtom2555
    Fin15AnchoredAtom2576 Fin15AnchoredAtom2716 Fin15AnchoredAtom4466 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 13, 14}, {0, 6, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 7, 14}, {0, 4, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29161 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom2717 chi ∧
      Fin15AnchoredAtom4467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2535 Fin15AnchoredAtom2536 Fin15AnchoredAtom2541
    Fin15AnchoredAtom2577 Fin15AnchoredAtom2717 Fin15AnchoredAtom4467 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 9, 10}, {0, 6, 8, 9, 10}, {0, 4, 8, 9, 10}, {0, 4, 6, 9, 10}, {0, 4, 6, 8, 10}, {0, 4, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29162 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2719 chi ∧
      Fin15AnchoredAtom4469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2535 Fin15AnchoredAtom2538 Fin15AnchoredAtom2543
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2719 Fin15AnchoredAtom4469 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 9, 12}, {0, 6, 8, 9, 12}, {0, 4, 8, 9, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29163 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom2720 chi ∧
      Fin15AnchoredAtom4470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2535 Fin15AnchoredAtom2539 Fin15AnchoredAtom2544
    Fin15AnchoredAtom2580 Fin15AnchoredAtom2720 Fin15AnchoredAtom4470 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 9, 13}, {0, 6, 8, 9, 13}, {0, 4, 8, 9, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29164 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom2721 chi ∧
      Fin15AnchoredAtom4471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2535 Fin15AnchoredAtom2540 Fin15AnchoredAtom2545
    Fin15AnchoredAtom2581 Fin15AnchoredAtom2721 Fin15AnchoredAtom4471 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 9, 14}, {0, 6, 8, 9, 14}, {0, 4, 8, 9, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29165 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom2723 chi ∧
      Fin15AnchoredAtom4473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2536 Fin15AnchoredAtom2538 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2583 Fin15AnchoredAtom2723 Fin15AnchoredAtom4473 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 10, 12}, {0, 6, 8, 10, 12}, {0, 4, 8, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 8, 12}, {0, 4, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29166 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2585 chi ∧
      Fin15AnchoredAtom2725 chi ∧
      Fin15AnchoredAtom4475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2536 Fin15AnchoredAtom2540 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2585 Fin15AnchoredAtom2725 Fin15AnchoredAtom4475 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 10, 14}, {0, 6, 8, 10, 14}, {0, 4, 8, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29167 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2589 chi ∧
      Fin15AnchoredAtom2729 chi ∧
      Fin15AnchoredAtom4479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2538 Fin15AnchoredAtom2539 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2589 Fin15AnchoredAtom2729 Fin15AnchoredAtom4479 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 12, 13}, {0, 6, 8, 12, 13}, {0, 4, 8, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 8, 13}, {0, 4, 6, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29168 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2590 chi ∧
      Fin15AnchoredAtom2730 chi ∧
      Fin15AnchoredAtom4480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2538 Fin15AnchoredAtom2540 Fin15AnchoredAtom2554
    Fin15AnchoredAtom2590 Fin15AnchoredAtom2730 Fin15AnchoredAtom4480 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 12, 14}, {0, 6, 8, 12, 14}, {0, 4, 8, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29169 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2591 chi ∧
      Fin15AnchoredAtom2731 chi ∧
      Fin15AnchoredAtom4481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2539 Fin15AnchoredAtom2540 Fin15AnchoredAtom2555
    Fin15AnchoredAtom2591 Fin15AnchoredAtom2731 Fin15AnchoredAtom4481 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 13, 14}, {0, 6, 8, 13, 14}, {0, 4, 8, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 8, 14}, {0, 4, 6, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29170 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2542 chi ∧
      Fin15AnchoredAtom2546 chi ∧
      Fin15AnchoredAtom2592 chi ∧
      Fin15AnchoredAtom2732 chi ∧
      Fin15AnchoredAtom4482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2541 Fin15AnchoredAtom2542 Fin15AnchoredAtom2546
    Fin15AnchoredAtom2592 Fin15AnchoredAtom2732 Fin15AnchoredAtom4482 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 9, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 11}, {0, 6, 9, 10, 11}, {0, 4, 9, 10, 11}, {0, 4, 6, 10, 11}, {0, 4, 6, 9, 11}, {0, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29171 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom4483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2541 Fin15AnchoredAtom2543 Fin15AnchoredAtom2547
    Fin15AnchoredAtom2593 Fin15AnchoredAtom2733 Fin15AnchoredAtom4483 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 4, 6, 10, 12}, {0, 4, 6, 9, 12}, {0, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29172 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom4484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2541 Fin15AnchoredAtom2544 Fin15AnchoredAtom2548
    Fin15AnchoredAtom2594 Fin15AnchoredAtom2734 Fin15AnchoredAtom4484 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29173 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom4485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2541 Fin15AnchoredAtom2545 Fin15AnchoredAtom2549
    Fin15AnchoredAtom2595 Fin15AnchoredAtom2735 Fin15AnchoredAtom4485 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29174 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom4489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2543 Fin15AnchoredAtom2544 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2599 Fin15AnchoredAtom2739 Fin15AnchoredAtom4489 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 9, 13}, {0, 4, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29175 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom4490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2543 Fin15AnchoredAtom2545 Fin15AnchoredAtom2554
    Fin15AnchoredAtom2600 Fin15AnchoredAtom2740 Fin15AnchoredAtom4490 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29176 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom4491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2544 Fin15AnchoredAtom2545 Fin15AnchoredAtom2555
    Fin15AnchoredAtom2601 Fin15AnchoredAtom2741 Fin15AnchoredAtom4491 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 9, 14}, {0, 4, 6, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29177 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2546 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2551 chi ∧
      Fin15AnchoredAtom2603 chi ∧
      Fin15AnchoredAtom2743 chi ∧
      Fin15AnchoredAtom4493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2546 Fin15AnchoredAtom2548 Fin15AnchoredAtom2551
    Fin15AnchoredAtom2603 Fin15AnchoredAtom2743 Fin15AnchoredAtom4493 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 10, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 11, 13}, {0, 6, 10, 11, 13}, {0, 4, 10, 11, 13}, {0, 4, 6, 11, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29178 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom4495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2547 Fin15AnchoredAtom2548 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2605 Fin15AnchoredAtom2745 Fin15AnchoredAtom4495 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 10, 13}, {0, 4, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29179 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom4496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2547 Fin15AnchoredAtom2549 Fin15AnchoredAtom2554
    Fin15AnchoredAtom2606 Fin15AnchoredAtom2746 Fin15AnchoredAtom4496 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29180 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom4497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2548 Fin15AnchoredAtom2549 Fin15AnchoredAtom2555
    Fin15AnchoredAtom2607 Fin15AnchoredAtom2747 Fin15AnchoredAtom4497 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 10, 14}, {0, 4, 6, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29181 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2550 chi ∧
      Fin15AnchoredAtom2551 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2608 chi ∧
      Fin15AnchoredAtom2748 chi ∧
      Fin15AnchoredAtom4498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2550 Fin15AnchoredAtom2551 Fin15AnchoredAtom2553
    Fin15AnchoredAtom2608 Fin15AnchoredAtom2748 Fin15AnchoredAtom4498 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 11, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 11, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 11, 12, 13}, {0, 6, 11, 12, 13}, {0, 4, 11, 12, 13}, {0, 4, 6, 12, 13}, {0, 4, 6, 11, 13}, {0, 4, 6, 11, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29182 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom4501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2553 Fin15AnchoredAtom2554 Fin15AnchoredAtom2555
    Fin15AnchoredAtom2611 Fin15AnchoredAtom2751 Fin15AnchoredAtom4501 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 4, 6, 13, 14}, {0, 4, 6, 12, 14}, {0, 4, 6, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29183 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom2754 chi ∧
      Fin15AnchoredAtom4504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2556 Fin15AnchoredAtom2559 Fin15AnchoredAtom2564
    Fin15AnchoredAtom2579 Fin15AnchoredAtom2754 Fin15AnchoredAtom4504 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 4, 7, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 4, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 4, 7, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 9, 12}, {0, 7, 8, 9, 12}, {0, 4, 8, 9, 12}, {0, 4, 7, 9, 12}, {0, 4, 7, 8, 12}, {0, 4, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
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
