module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 224. -/

theorem fin15Anchored_clause28672 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom3574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2112 Fin15AnchoredAtom2115 Fin15AnchoredAtom2154
    Fin15AnchoredAtom2199 Fin15AnchoredAtom2364 Fin15AnchoredAtom3574 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 10, 13}, {0, 3, 4, 10, 13}, {0, 2, 4, 10, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28673 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2112 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom3575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2112 Fin15AnchoredAtom2116 Fin15AnchoredAtom2155
    Fin15AnchoredAtom2200 Fin15AnchoredAtom2365 Fin15AnchoredAtom3575 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 10, 14}, {0, 3, 4, 10, 14}, {0, 2, 4, 10, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28674 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom3579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2114 Fin15AnchoredAtom2115 Fin15AnchoredAtom2159
    Fin15AnchoredAtom2204 Fin15AnchoredAtom2369 Fin15AnchoredAtom3579 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 12, 13}, {0, 3, 4, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 3, 12, 13}, {0, 2, 3, 4, 13}, {0, 2, 3, 4, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28675 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2114 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom3580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2114 Fin15AnchoredAtom2116 Fin15AnchoredAtom2160
    Fin15AnchoredAtom2205 Fin15AnchoredAtom2370 Fin15AnchoredAtom3580 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 12, 14}, {0, 3, 4, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28676 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2115 chi ∧
      Fin15AnchoredAtom2116 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom3581 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2115 Fin15AnchoredAtom2116 Fin15AnchoredAtom2161
    Fin15AnchoredAtom2206 Fin15AnchoredAtom2371 Fin15AnchoredAtom3581 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 4, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 4, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 4, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 4, 13, 14}, {0, 3, 4, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 3, 13, 14}, {0, 2, 3, 4, 14}, {0, 2, 3, 4, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28677 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom3582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2118 Fin15AnchoredAtom2126
    Fin15AnchoredAtom2207 Fin15AnchoredAtom2372 Fin15AnchoredAtom3582 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 7}, {0, 3, 5, 6, 7}, {0, 2, 5, 6, 7}, {0, 2, 3, 6, 7}, {0, 2, 3, 5, 7}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28678 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom3584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2120 Fin15AnchoredAtom2128
    Fin15AnchoredAtom2209 Fin15AnchoredAtom2374 Fin15AnchoredAtom3584 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 9}, {0, 3, 5, 6, 9}, {0, 2, 5, 6, 9}, {0, 2, 3, 6, 9}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28679 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom3585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2121 Fin15AnchoredAtom2129
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2375 Fin15AnchoredAtom3585 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 10}, {0, 3, 5, 6, 10}, {0, 2, 5, 6, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28680 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom3587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2123 Fin15AnchoredAtom2131
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2377 Fin15AnchoredAtom3587 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 12}, {0, 3, 5, 6, 12}, {0, 2, 5, 6, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28681 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom3588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2124 Fin15AnchoredAtom2132
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2378 Fin15AnchoredAtom3588 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 13}, {0, 3, 5, 6, 13}, {0, 2, 5, 6, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28682 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2117 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom3589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2117 Fin15AnchoredAtom2125 Fin15AnchoredAtom2133
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2379 Fin15AnchoredAtom3589 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 6, 14}, {0, 3, 5, 6, 14}, {0, 2, 5, 6, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28683 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2215 chi ∧
      Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom3590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2119 Fin15AnchoredAtom2134
    Fin15AnchoredAtom2215 Fin15AnchoredAtom2380 Fin15AnchoredAtom3590 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 8}, {0, 3, 5, 7, 8}, {0, 2, 5, 7, 8}, {0, 2, 3, 7, 8}, {0, 2, 3, 5, 8}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28684 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom3591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2120 Fin15AnchoredAtom2135
    Fin15AnchoredAtom2216 Fin15AnchoredAtom2381 Fin15AnchoredAtom3591 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 9}, {0, 3, 5, 7, 9}, {0, 2, 5, 7, 9}, {0, 2, 3, 7, 9}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28685 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom3592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2121 Fin15AnchoredAtom2136
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2382 Fin15AnchoredAtom3592 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 10}, {0, 3, 5, 7, 10}, {0, 2, 5, 7, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28686 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2218 chi ∧
      Fin15AnchoredAtom2383 chi ∧
      Fin15AnchoredAtom3593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2122 Fin15AnchoredAtom2137
    Fin15AnchoredAtom2218 Fin15AnchoredAtom2383 Fin15AnchoredAtom3593 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 7, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 7, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 7, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 11}, {0, 3, 5, 7, 11}, {0, 2, 5, 7, 11}, {0, 2, 3, 7, 11}, {0, 2, 3, 5, 11}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28687 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom3594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2123 Fin15AnchoredAtom2138
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2384 Fin15AnchoredAtom3594 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 12}, {0, 3, 5, 7, 12}, {0, 2, 5, 7, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28688 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom3595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2124 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2385 Fin15AnchoredAtom3595 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 13}, {0, 3, 5, 7, 13}, {0, 2, 5, 7, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28689 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2118 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom3596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2118 Fin15AnchoredAtom2125 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2386 Fin15AnchoredAtom3596 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 7, 14}, {0, 3, 5, 7, 14}, {0, 2, 5, 7, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28690 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom2222 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom3597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2119 Fin15AnchoredAtom2120 Fin15AnchoredAtom2141
    Fin15AnchoredAtom2222 Fin15AnchoredAtom2387 Fin15AnchoredAtom3597 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 8, 9}, {0, 3, 5, 8, 9}, {0, 2, 5, 8, 9}, {0, 2, 3, 8, 9}, {0, 2, 3, 5, 9}, {0, 2, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28691 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2223 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom3598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2119 Fin15AnchoredAtom2121 Fin15AnchoredAtom2142
    Fin15AnchoredAtom2223 Fin15AnchoredAtom2388 Fin15AnchoredAtom3598 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 8, 10}, {0, 3, 5, 8, 10}, {0, 2, 5, 8, 10}, {0, 2, 3, 8, 10}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28692 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2119 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2146 chi ∧
      Fin15AnchoredAtom2227 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom3602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2119 Fin15AnchoredAtom2125 Fin15AnchoredAtom2146
    Fin15AnchoredAtom2227 Fin15AnchoredAtom2392 Fin15AnchoredAtom3602 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 8, 14}, {0, 3, 5, 8, 14}, {0, 2, 5, 8, 14}, {0, 2, 3, 8, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28693 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom3603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2120 Fin15AnchoredAtom2121 Fin15AnchoredAtom2147
    Fin15AnchoredAtom2228 Fin15AnchoredAtom2393 Fin15AnchoredAtom3603 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 9, 10}, {0, 3, 5, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 3, 9, 10}, {0, 2, 3, 5, 10}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28694 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom3605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2120 Fin15AnchoredAtom2123 Fin15AnchoredAtom2149
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2395 Fin15AnchoredAtom3605 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 9, 12}, {0, 3, 5, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28695 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom3606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2120 Fin15AnchoredAtom2124 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2396 Fin15AnchoredAtom3606 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 9, 13}, {0, 3, 5, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28696 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2120 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom3607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2120 Fin15AnchoredAtom2125 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2232 Fin15AnchoredAtom2397 Fin15AnchoredAtom3607 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 9, 14}, {0, 3, 5, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28697 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2122 chi ∧
      Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom2233 chi ∧
      Fin15AnchoredAtom2398 chi ∧
      Fin15AnchoredAtom3608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2121 Fin15AnchoredAtom2122 Fin15AnchoredAtom2152
    Fin15AnchoredAtom2233 Fin15AnchoredAtom2398 Fin15AnchoredAtom3608 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 10, 11}, {0, 3, 5, 10, 11}, {0, 2, 5, 10, 11}, {0, 2, 3, 10, 11}, {0, 2, 3, 5, 11}, {0, 2, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28698 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom3609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2121 Fin15AnchoredAtom2123 Fin15AnchoredAtom2153
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2399 Fin15AnchoredAtom3609 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 10, 12}, {0, 3, 5, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 3, 10, 12}, {0, 2, 3, 5, 12}, {0, 2, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28699 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom3610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2121 Fin15AnchoredAtom2124 Fin15AnchoredAtom2154
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2400 Fin15AnchoredAtom3610 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 10, 13}, {0, 3, 5, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28700 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2121 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom3611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2121 Fin15AnchoredAtom2125 Fin15AnchoredAtom2155
    Fin15AnchoredAtom2236 Fin15AnchoredAtom2401 Fin15AnchoredAtom3611 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 10, 14}, {0, 3, 5, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28701 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom3615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2123 Fin15AnchoredAtom2124 Fin15AnchoredAtom2159
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2405 Fin15AnchoredAtom3615 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 12, 13}, {0, 3, 5, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 3, 12, 13}, {0, 2, 3, 5, 13}, {0, 2, 3, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28702 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2123 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom3616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2123 Fin15AnchoredAtom2125 Fin15AnchoredAtom2160
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2406 Fin15AnchoredAtom3616 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 12, 14}, {0, 3, 5, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28703 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2124 chi ∧
      Fin15AnchoredAtom2125 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom3617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2124 Fin15AnchoredAtom2125 Fin15AnchoredAtom2161
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2407 Fin15AnchoredAtom3617 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 5, 13, 14}, {0, 3, 5, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 3, 13, 14}, {0, 2, 3, 5, 14}, {0, 2, 3, 5, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28704 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom3619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2126 Fin15AnchoredAtom2128 Fin15AnchoredAtom2135
    Fin15AnchoredAtom2244 Fin15AnchoredAtom2409 Fin15AnchoredAtom3619 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 9}, {0, 3, 6, 7, 9}, {0, 2, 6, 7, 9}, {0, 2, 3, 7, 9}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28705 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom3620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2126 Fin15AnchoredAtom2129 Fin15AnchoredAtom2136
    Fin15AnchoredAtom2245 Fin15AnchoredAtom2410 Fin15AnchoredAtom3620 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 10}, {0, 3, 6, 7, 10}, {0, 2, 6, 7, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28706 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2130 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2246 chi ∧
      Fin15AnchoredAtom2411 chi ∧
      Fin15AnchoredAtom3621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2126 Fin15AnchoredAtom2130 Fin15AnchoredAtom2137
    Fin15AnchoredAtom2246 Fin15AnchoredAtom2411 Fin15AnchoredAtom3621 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 7, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 7, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 7, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 11}, {0, 3, 6, 7, 11}, {0, 2, 6, 7, 11}, {0, 2, 3, 7, 11}, {0, 2, 3, 6, 11}, {0, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28707 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom3622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2126 Fin15AnchoredAtom2131 Fin15AnchoredAtom2138
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2412 Fin15AnchoredAtom3622 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 12}, {0, 3, 6, 7, 12}, {0, 2, 6, 7, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28708 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom3623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2126 Fin15AnchoredAtom2132 Fin15AnchoredAtom2139
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2413 Fin15AnchoredAtom3623 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 13}, {0, 3, 6, 7, 13}, {0, 2, 6, 7, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28709 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2126 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom3624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2126 Fin15AnchoredAtom2133 Fin15AnchoredAtom2140
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2414 Fin15AnchoredAtom3624 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 7, 14}, {0, 3, 6, 7, 14}, {0, 2, 6, 7, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28710 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2127 chi ∧
      Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom2250 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom3625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2127 Fin15AnchoredAtom2128 Fin15AnchoredAtom2141
    Fin15AnchoredAtom2250 Fin15AnchoredAtom2415 Fin15AnchoredAtom3625 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 8, 9}, {0, 3, 6, 8, 9}, {0, 2, 6, 8, 9}, {0, 2, 3, 8, 9}, {0, 2, 3, 6, 9}, {0, 2, 3, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28711 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2127 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2251 chi ∧
      Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom3626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2127 Fin15AnchoredAtom2129 Fin15AnchoredAtom2142
    Fin15AnchoredAtom2251 Fin15AnchoredAtom2416 Fin15AnchoredAtom3626 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 8, 10}, {0, 3, 6, 8, 10}, {0, 2, 6, 8, 10}, {0, 2, 3, 8, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28712 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2127 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2144 chi ∧
      Fin15AnchoredAtom2253 chi ∧
      Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom3628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2127 Fin15AnchoredAtom2131 Fin15AnchoredAtom2144
    Fin15AnchoredAtom2253 Fin15AnchoredAtom2418 Fin15AnchoredAtom3628 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 8, 12}, {0, 3, 6, 8, 12}, {0, 2, 6, 8, 12}, {0, 2, 3, 8, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28713 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom3631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2128 Fin15AnchoredAtom2129 Fin15AnchoredAtom2147
    Fin15AnchoredAtom2256 Fin15AnchoredAtom2421 Fin15AnchoredAtom3631 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 9, 10}, {0, 3, 6, 9, 10}, {0, 2, 6, 9, 10}, {0, 2, 3, 9, 10}, {0, 2, 3, 6, 10}, {0, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28714 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom3633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2128 Fin15AnchoredAtom2131 Fin15AnchoredAtom2149
    Fin15AnchoredAtom2258 Fin15AnchoredAtom2423 Fin15AnchoredAtom3633 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 9, 12}, {0, 3, 6, 9, 12}, {0, 2, 6, 9, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28715 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom3634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2128 Fin15AnchoredAtom2132 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2424 Fin15AnchoredAtom3634 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 9, 13}, {0, 3, 6, 9, 13}, {0, 2, 6, 9, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28716 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2128 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom3635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2128 Fin15AnchoredAtom2133 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2425 Fin15AnchoredAtom3635 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 9, 14}, {0, 3, 6, 9, 14}, {0, 2, 6, 9, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28717 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2130 chi ∧
      Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom2261 chi ∧
      Fin15AnchoredAtom2426 chi ∧
      Fin15AnchoredAtom3636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2129 Fin15AnchoredAtom2130 Fin15AnchoredAtom2152
    Fin15AnchoredAtom2261 Fin15AnchoredAtom2426 Fin15AnchoredAtom3636 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 10, 11}, {0, 3, 6, 10, 11}, {0, 2, 6, 10, 11}, {0, 2, 3, 10, 11}, {0, 2, 3, 6, 11}, {0, 2, 3, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28718 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom3637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2129 Fin15AnchoredAtom2131 Fin15AnchoredAtom2153
    Fin15AnchoredAtom2262 Fin15AnchoredAtom2427 Fin15AnchoredAtom3637 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 10, 12}, {0, 3, 6, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 3, 10, 12}, {0, 2, 3, 6, 12}, {0, 2, 3, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28719 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2428 chi ∧
      Fin15AnchoredAtom3638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2129 Fin15AnchoredAtom2132 Fin15AnchoredAtom2154
    Fin15AnchoredAtom2263 Fin15AnchoredAtom2428 Fin15AnchoredAtom3638 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 10, 13}, {0, 3, 6, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28720 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2129 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2429 chi ∧
      Fin15AnchoredAtom3639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2129 Fin15AnchoredAtom2133 Fin15AnchoredAtom2155
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2429 Fin15AnchoredAtom3639 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 10, 14}, {0, 3, 6, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28721 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2130 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2157 chi ∧
      Fin15AnchoredAtom2266 chi ∧
      Fin15AnchoredAtom2431 chi ∧
      Fin15AnchoredAtom3641 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2130 Fin15AnchoredAtom2132 Fin15AnchoredAtom2157
    Fin15AnchoredAtom2266 Fin15AnchoredAtom2431 Fin15AnchoredAtom3641 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 11, 13}, {0, 3, 6, 11, 13}, {0, 2, 6, 11, 13}, {0, 2, 3, 11, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28722 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2433 chi ∧
      Fin15AnchoredAtom3643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2131 Fin15AnchoredAtom2132 Fin15AnchoredAtom2159
    Fin15AnchoredAtom2268 Fin15AnchoredAtom2433 Fin15AnchoredAtom3643 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 12, 13}, {0, 3, 6, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 3, 12, 13}, {0, 2, 3, 6, 13}, {0, 2, 3, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28723 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2131 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2434 chi ∧
      Fin15AnchoredAtom3644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2131 Fin15AnchoredAtom2133 Fin15AnchoredAtom2160
    Fin15AnchoredAtom2269 Fin15AnchoredAtom2434 Fin15AnchoredAtom3644 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 12, 14}, {0, 3, 6, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28724 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2132 chi ∧
      Fin15AnchoredAtom2133 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2435 chi ∧
      Fin15AnchoredAtom3645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2132 Fin15AnchoredAtom2133 Fin15AnchoredAtom2161
    Fin15AnchoredAtom2270 Fin15AnchoredAtom2435 Fin15AnchoredAtom3645 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 6, 13, 14}, {0, 3, 6, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 3, 13, 14}, {0, 2, 3, 6, 14}, {0, 2, 3, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28725 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2272 chi ∧
      Fin15AnchoredAtom2437 chi ∧
      Fin15AnchoredAtom3647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2134 Fin15AnchoredAtom2136 Fin15AnchoredAtom2142
    Fin15AnchoredAtom2272 Fin15AnchoredAtom2437 Fin15AnchoredAtom3647 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 8, 10}, {0, 3, 7, 8, 10}, {0, 2, 7, 8, 10}, {0, 2, 3, 8, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28726 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2134 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2146 chi ∧
      Fin15AnchoredAtom2276 chi ∧
      Fin15AnchoredAtom2441 chi ∧
      Fin15AnchoredAtom3651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2134 Fin15AnchoredAtom2140 Fin15AnchoredAtom2146
    Fin15AnchoredAtom2276 Fin15AnchoredAtom2441 Fin15AnchoredAtom3651 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 8, 14}, {0, 3, 7, 8, 14}, {0, 2, 7, 8, 14}, {0, 2, 3, 8, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28727 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2442 chi ∧
      Fin15AnchoredAtom3652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2135 Fin15AnchoredAtom2136 Fin15AnchoredAtom2147
    Fin15AnchoredAtom2277 Fin15AnchoredAtom2442 Fin15AnchoredAtom3652 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 9, 10}, {0, 3, 7, 9, 10}, {0, 2, 7, 9, 10}, {0, 2, 3, 9, 10}, {0, 2, 3, 7, 10}, {0, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28728 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2148 chi ∧
      Fin15AnchoredAtom2278 chi ∧
      Fin15AnchoredAtom2443 chi ∧
      Fin15AnchoredAtom3653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2135 Fin15AnchoredAtom2137 Fin15AnchoredAtom2148
    Fin15AnchoredAtom2278 Fin15AnchoredAtom2443 Fin15AnchoredAtom3653 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 9, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 9, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 9, 11}, {0, 3, 7, 9, 11}, {0, 2, 7, 9, 11}, {0, 2, 3, 9, 11}, {0, 2, 3, 7, 11}, {0, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28729 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2444 chi ∧
      Fin15AnchoredAtom3654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2135 Fin15AnchoredAtom2138 Fin15AnchoredAtom2149
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2444 Fin15AnchoredAtom3654 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 9, 12}, {0, 3, 7, 9, 12}, {0, 2, 7, 9, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28730 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2445 chi ∧
      Fin15AnchoredAtom3655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2135 Fin15AnchoredAtom2139 Fin15AnchoredAtom2150
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2445 Fin15AnchoredAtom3655 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 9, 13}, {0, 3, 7, 9, 13}, {0, 2, 7, 9, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28731 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2135 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2446 chi ∧
      Fin15AnchoredAtom3656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2135 Fin15AnchoredAtom2140 Fin15AnchoredAtom2151
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2446 Fin15AnchoredAtom3656 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 9, 14}, {0, 3, 7, 9, 14}, {0, 2, 7, 9, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28732 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2152 chi ∧
      Fin15AnchoredAtom2282 chi ∧
      Fin15AnchoredAtom2447 chi ∧
      Fin15AnchoredAtom3657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2136 Fin15AnchoredAtom2137 Fin15AnchoredAtom2152
    Fin15AnchoredAtom2282 Fin15AnchoredAtom2447 Fin15AnchoredAtom3657 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 10, 11}, {0, 3, 7, 10, 11}, {0, 2, 7, 10, 11}, {0, 2, 3, 10, 11}, {0, 2, 3, 7, 11}, {0, 2, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28733 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2448 chi ∧
      Fin15AnchoredAtom3658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2136 Fin15AnchoredAtom2138 Fin15AnchoredAtom2153
    Fin15AnchoredAtom2283 Fin15AnchoredAtom2448 Fin15AnchoredAtom3658 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 10, 12}, {0, 3, 7, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 3, 10, 12}, {0, 2, 3, 7, 12}, {0, 2, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28734 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2449 chi ∧
      Fin15AnchoredAtom3659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2136 Fin15AnchoredAtom2139 Fin15AnchoredAtom2154
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2449 Fin15AnchoredAtom3659 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 10, 13}, {0, 3, 7, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28735 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2136 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2450 chi ∧
      Fin15AnchoredAtom3660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2136 Fin15AnchoredAtom2140 Fin15AnchoredAtom2155
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2450 Fin15AnchoredAtom3660 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 10, 14}, {0, 3, 7, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28736 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2137 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2158 chi ∧
      Fin15AnchoredAtom2288 chi ∧
      Fin15AnchoredAtom2453 chi ∧
      Fin15AnchoredAtom3663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2137 Fin15AnchoredAtom2140 Fin15AnchoredAtom2158
    Fin15AnchoredAtom2288 Fin15AnchoredAtom2453 Fin15AnchoredAtom3663 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 11, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 11, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 11, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 11, 14}, {0, 3, 7, 11, 14}, {0, 2, 7, 11, 14}, {0, 2, 3, 11, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28737 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2454 chi ∧
      Fin15AnchoredAtom3664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2138 Fin15AnchoredAtom2139 Fin15AnchoredAtom2159
    Fin15AnchoredAtom2289 Fin15AnchoredAtom2454 Fin15AnchoredAtom3664 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 12, 13}, {0, 3, 7, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 3, 12, 13}, {0, 2, 3, 7, 13}, {0, 2, 3, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28738 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2138 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2455 chi ∧
      Fin15AnchoredAtom3665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2138 Fin15AnchoredAtom2140 Fin15AnchoredAtom2160
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2455 Fin15AnchoredAtom3665 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 12, 14}, {0, 3, 7, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28739 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2139 chi ∧
      Fin15AnchoredAtom2140 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2456 chi ∧
      Fin15AnchoredAtom3666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2139 Fin15AnchoredAtom2140 Fin15AnchoredAtom2161
    Fin15AnchoredAtom2291 Fin15AnchoredAtom2456 Fin15AnchoredAtom3666 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 7, 13, 14}, {0, 3, 7, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 3, 13, 14}, {0, 2, 3, 7, 14}, {0, 2, 3, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28740 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2141 chi ∧
      Fin15AnchoredAtom2142 chi ∧
      Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2292 chi ∧
      Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom3667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2141 Fin15AnchoredAtom2142 Fin15AnchoredAtom2147
    Fin15AnchoredAtom2292 Fin15AnchoredAtom2457 Fin15AnchoredAtom3667 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 8, 9, 10}, {0, 3, 8, 9, 10}, {0, 2, 8, 9, 10}, {0, 2, 3, 9, 10}, {0, 2, 3, 8, 10}, {0, 2, 3, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28741 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom3683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2147 Fin15AnchoredAtom2149 Fin15AnchoredAtom2153
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2473 Fin15AnchoredAtom3683 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 10, 12}, {0, 3, 9, 10, 12}, {0, 2, 9, 10, 12}, {0, 2, 3, 10, 12}, {0, 2, 3, 9, 12}, {0, 2, 3, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28742 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom3684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2147 Fin15AnchoredAtom2150 Fin15AnchoredAtom2154
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2474 Fin15AnchoredAtom3684 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 10, 13}, {0, 3, 9, 10, 13}, {0, 2, 9, 10, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28743 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2147 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom3685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2147 Fin15AnchoredAtom2151 Fin15AnchoredAtom2155
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2475 Fin15AnchoredAtom3685 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 10, 14}, {0, 3, 9, 10, 14}, {0, 2, 9, 10, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28744 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom3689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2149 Fin15AnchoredAtom2150 Fin15AnchoredAtom2159
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2479 Fin15AnchoredAtom3689 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 12, 13}, {0, 3, 9, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 3, 12, 13}, {0, 2, 3, 9, 13}, {0, 2, 3, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28745 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2149 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom3690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2149 Fin15AnchoredAtom2151 Fin15AnchoredAtom2160
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2480 Fin15AnchoredAtom3690 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 12, 14}, {0, 3, 9, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28746 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2150 chi ∧
      Fin15AnchoredAtom2151 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom3691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2150 Fin15AnchoredAtom2151 Fin15AnchoredAtom2161
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2481 Fin15AnchoredAtom3691 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 9, 13, 14}, {0, 3, 9, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 3, 13, 14}, {0, 2, 3, 9, 14}, {0, 2, 3, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28747 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom3695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2153 Fin15AnchoredAtom2154 Fin15AnchoredAtom2159
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2485 Fin15AnchoredAtom3695 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 10, 12, 13}, {0, 3, 10, 12, 13}, {0, 2, 10, 12, 13}, {0, 2, 3, 12, 13}, {0, 2, 3, 10, 13}, {0, 2, 3, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28748 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2153 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom3696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2153 Fin15AnchoredAtom2155 Fin15AnchoredAtom2160
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2486 Fin15AnchoredAtom3696 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 10, 12, 14}, {0, 3, 10, 12, 14}, {0, 2, 10, 12, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28749 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2154 chi ∧
      Fin15AnchoredAtom2155 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom3697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2154 Fin15AnchoredAtom2155 Fin15AnchoredAtom2161
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2487 Fin15AnchoredAtom3697 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 10, 13, 14}, {0, 3, 10, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 3, 13, 14}, {0, 2, 3, 10, 14}, {0, 2, 3, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28750 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2159 chi ∧
      Fin15AnchoredAtom2160 chi ∧
      Fin15AnchoredAtom2161 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom3701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2159 Fin15AnchoredAtom2160 Fin15AnchoredAtom2161
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2491 Fin15AnchoredAtom3701 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 3, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 3, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 3, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 3, 12, 13, 14}, {0, 3, 12, 13, 14}, {0, 2, 12, 13, 14}, {0, 2, 3, 13, 14}, {0, 2, 3, 12, 14}, {0, 2, 3, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28751 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom3702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2162 Fin15AnchoredAtom2163 Fin15AnchoredAtom2171
    Fin15AnchoredAtom2207 Fin15AnchoredAtom2492 Fin15AnchoredAtom3702 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 7}, {0, 4, 5, 6, 7}, {0, 2, 5, 6, 7}, {0, 2, 4, 6, 7}, {0, 2, 4, 5, 7}, {0, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28752 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom3704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2162 Fin15AnchoredAtom2165 Fin15AnchoredAtom2173
    Fin15AnchoredAtom2209 Fin15AnchoredAtom2494 Fin15AnchoredAtom3704 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 9}, {0, 4, 5, 6, 9}, {0, 2, 5, 6, 9}, {0, 2, 4, 6, 9}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28753 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom3705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2162 Fin15AnchoredAtom2166 Fin15AnchoredAtom2174
    Fin15AnchoredAtom2210 Fin15AnchoredAtom2495 Fin15AnchoredAtom3705 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 10}, {0, 4, 5, 6, 10}, {0, 2, 5, 6, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28754 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom3707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2162 Fin15AnchoredAtom2168 Fin15AnchoredAtom2176
    Fin15AnchoredAtom2212 Fin15AnchoredAtom2497 Fin15AnchoredAtom3707 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 12}, {0, 4, 5, 6, 12}, {0, 2, 5, 6, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28755 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom3708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2162 Fin15AnchoredAtom2169 Fin15AnchoredAtom2177
    Fin15AnchoredAtom2213 Fin15AnchoredAtom2498 Fin15AnchoredAtom3708 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 13}, {0, 4, 5, 6, 13}, {0, 2, 5, 6, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28756 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2162 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom3709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2162 Fin15AnchoredAtom2170 Fin15AnchoredAtom2178
    Fin15AnchoredAtom2214 Fin15AnchoredAtom2499 Fin15AnchoredAtom3709 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 6, 14}, {0, 4, 5, 6, 14}, {0, 2, 5, 6, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28757 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom3711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2163 Fin15AnchoredAtom2165 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2216 Fin15AnchoredAtom2501 Fin15AnchoredAtom3711 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 9}, {0, 4, 5, 7, 9}, {0, 2, 5, 7, 9}, {0, 2, 4, 7, 9}, {0, 2, 4, 5, 9}, {0, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28758 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom3712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2163 Fin15AnchoredAtom2166 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2217 Fin15AnchoredAtom2502 Fin15AnchoredAtom3712 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 10}, {0, 4, 5, 7, 10}, {0, 2, 5, 7, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28759 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom3714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2163 Fin15AnchoredAtom2168 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2219 Fin15AnchoredAtom2504 Fin15AnchoredAtom3714 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 12}, {0, 4, 5, 7, 12}, {0, 2, 5, 7, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28760 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom3715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2163 Fin15AnchoredAtom2169 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2220 Fin15AnchoredAtom2505 Fin15AnchoredAtom3715 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 13}, {0, 4, 5, 7, 13}, {0, 2, 5, 7, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28761 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2163 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom3716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2163 Fin15AnchoredAtom2170 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2221 Fin15AnchoredAtom2506 Fin15AnchoredAtom3716 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 7, 14}, {0, 4, 5, 7, 14}, {0, 2, 5, 7, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28762 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom3723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2165 Fin15AnchoredAtom2166 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2228 Fin15AnchoredAtom2513 Fin15AnchoredAtom3723 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 9, 10}, {0, 4, 5, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 4, 9, 10}, {0, 2, 4, 5, 10}, {0, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28763 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom3725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2165 Fin15AnchoredAtom2168 Fin15AnchoredAtom2194
    Fin15AnchoredAtom2230 Fin15AnchoredAtom2515 Fin15AnchoredAtom3725 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 9, 12}, {0, 4, 5, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28764 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom3726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2165 Fin15AnchoredAtom2169 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2231 Fin15AnchoredAtom2516 Fin15AnchoredAtom3726 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 9, 13}, {0, 4, 5, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28765 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2165 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom3727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2165 Fin15AnchoredAtom2170 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2232 Fin15AnchoredAtom2517 Fin15AnchoredAtom3727 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 9, 14}, {0, 4, 5, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28766 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom3729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2166 Fin15AnchoredAtom2168 Fin15AnchoredAtom2198
    Fin15AnchoredAtom2234 Fin15AnchoredAtom2519 Fin15AnchoredAtom3729 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 10, 12}, {0, 4, 5, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 4, 10, 12}, {0, 2, 4, 5, 12}, {0, 2, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28767 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom3730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2166 Fin15AnchoredAtom2169 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2235 Fin15AnchoredAtom2520 Fin15AnchoredAtom3730 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 10, 13}, {0, 4, 5, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28768 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2166 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom3731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2166 Fin15AnchoredAtom2170 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2236 Fin15AnchoredAtom2521 Fin15AnchoredAtom3731 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 10, 14}, {0, 4, 5, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28769 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom3735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2168 Fin15AnchoredAtom2169 Fin15AnchoredAtom2204
    Fin15AnchoredAtom2240 Fin15AnchoredAtom2525 Fin15AnchoredAtom3735 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 12, 13}, {0, 4, 5, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 5, 13}, {0, 2, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28770 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2168 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom3736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2168 Fin15AnchoredAtom2170 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2241 Fin15AnchoredAtom2526 Fin15AnchoredAtom3736 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 12, 14}, {0, 4, 5, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28771 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2169 chi ∧
      Fin15AnchoredAtom2170 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom3737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2169 Fin15AnchoredAtom2170 Fin15AnchoredAtom2206
    Fin15AnchoredAtom2242 Fin15AnchoredAtom2527 Fin15AnchoredAtom3737 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 5, 13, 14}, {0, 4, 5, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 5, 14}, {0, 2, 4, 5, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28772 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2172 chi ∧
      Fin15AnchoredAtom2179 chi ∧
      Fin15AnchoredAtom2243 chi ∧
      Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom3738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2171 Fin15AnchoredAtom2172 Fin15AnchoredAtom2179
    Fin15AnchoredAtom2243 Fin15AnchoredAtom2528 Fin15AnchoredAtom3738 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 8}, {0, 4, 6, 7, 8}, {0, 2, 6, 7, 8}, {0, 2, 4, 7, 8}, {0, 2, 4, 6, 8}, {0, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28773 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom3739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2171 Fin15AnchoredAtom2173 Fin15AnchoredAtom2180
    Fin15AnchoredAtom2244 Fin15AnchoredAtom2529 Fin15AnchoredAtom3739 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 9}, {0, 4, 6, 7, 9}, {0, 2, 6, 7, 9}, {0, 2, 4, 7, 9}, {0, 2, 4, 6, 9}, {0, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28774 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom3740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2171 Fin15AnchoredAtom2174 Fin15AnchoredAtom2181
    Fin15AnchoredAtom2245 Fin15AnchoredAtom2530 Fin15AnchoredAtom3740 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 10}, {0, 4, 6, 7, 10}, {0, 2, 6, 7, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28775 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom3742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2171 Fin15AnchoredAtom2176 Fin15AnchoredAtom2183
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2532 Fin15AnchoredAtom3742 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 12}, {0, 4, 6, 7, 12}, {0, 2, 6, 7, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28776 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom3743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2171 Fin15AnchoredAtom2177 Fin15AnchoredAtom2184
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2533 Fin15AnchoredAtom3743 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 13}, {0, 4, 6, 7, 13}, {0, 2, 6, 7, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28777 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2171 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom3744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2171 Fin15AnchoredAtom2178 Fin15AnchoredAtom2185
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2534 Fin15AnchoredAtom3744 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 7, 14}, {0, 4, 6, 7, 14}, {0, 2, 6, 7, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28778 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom3751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2173 Fin15AnchoredAtom2174 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2256 Fin15AnchoredAtom2541 Fin15AnchoredAtom3751 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 9, 10}, {0, 4, 6, 9, 10}, {0, 2, 6, 9, 10}, {0, 2, 4, 9, 10}, {0, 2, 4, 6, 10}, {0, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28779 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom3753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2173 Fin15AnchoredAtom2176 Fin15AnchoredAtom2194
    Fin15AnchoredAtom2258 Fin15AnchoredAtom2543 Fin15AnchoredAtom3753 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 9, 12}, {0, 4, 6, 9, 12}, {0, 2, 6, 9, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28780 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom3754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2173 Fin15AnchoredAtom2177 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2544 Fin15AnchoredAtom3754 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 9, 13}, {0, 4, 6, 9, 13}, {0, 2, 6, 9, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28781 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2173 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom3755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2173 Fin15AnchoredAtom2178 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2545 Fin15AnchoredAtom3755 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 9, 14}, {0, 4, 6, 9, 14}, {0, 2, 6, 9, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28782 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom3757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2174 Fin15AnchoredAtom2176 Fin15AnchoredAtom2198
    Fin15AnchoredAtom2262 Fin15AnchoredAtom2547 Fin15AnchoredAtom3757 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 10, 12}, {0, 4, 6, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 4, 10, 12}, {0, 2, 4, 6, 12}, {0, 2, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28783 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom3758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2174 Fin15AnchoredAtom2177 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2263 Fin15AnchoredAtom2548 Fin15AnchoredAtom3758 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 10, 13}, {0, 4, 6, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28784 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2174 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom3759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2174 Fin15AnchoredAtom2178 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2549 Fin15AnchoredAtom3759 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 10, 14}, {0, 4, 6, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28785 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom3763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2176 Fin15AnchoredAtom2177 Fin15AnchoredAtom2204
    Fin15AnchoredAtom2268 Fin15AnchoredAtom2553 Fin15AnchoredAtom3763 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 12, 13}, {0, 4, 6, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 6, 13}, {0, 2, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28786 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2176 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom3764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2176 Fin15AnchoredAtom2178 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2269 Fin15AnchoredAtom2554 Fin15AnchoredAtom3764 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 12, 14}, {0, 4, 6, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28787 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2177 chi ∧
      Fin15AnchoredAtom2178 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom3765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2177 Fin15AnchoredAtom2178 Fin15AnchoredAtom2206
    Fin15AnchoredAtom2270 Fin15AnchoredAtom2555 Fin15AnchoredAtom3765 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 6, 13, 14}, {0, 4, 6, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 6, 14}, {0, 2, 4, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28788 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2179 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2187 chi ∧
      Fin15AnchoredAtom2272 chi ∧
      Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom3767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2179 Fin15AnchoredAtom2181 Fin15AnchoredAtom2187
    Fin15AnchoredAtom2272 Fin15AnchoredAtom2557 Fin15AnchoredAtom3767 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 8, 10}, {0, 4, 7, 8, 10}, {0, 2, 7, 8, 10}, {0, 2, 4, 8, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28789 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom3772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2180 Fin15AnchoredAtom2181 Fin15AnchoredAtom2192
    Fin15AnchoredAtom2277 Fin15AnchoredAtom2562 Fin15AnchoredAtom3772 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 9, 10}, {0, 4, 7, 9, 10}, {0, 2, 7, 9, 10}, {0, 2, 4, 9, 10}, {0, 2, 4, 7, 10}, {0, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28790 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom3774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2180 Fin15AnchoredAtom2183 Fin15AnchoredAtom2194
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2564 Fin15AnchoredAtom3774 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 9, 12}, {0, 4, 7, 9, 12}, {0, 2, 7, 9, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28791 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom3775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2180 Fin15AnchoredAtom2184 Fin15AnchoredAtom2195
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2565 Fin15AnchoredAtom3775 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 9, 13}, {0, 4, 7, 9, 13}, {0, 2, 7, 9, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28792 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2180 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom3776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2180 Fin15AnchoredAtom2185 Fin15AnchoredAtom2196
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2566 Fin15AnchoredAtom3776 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 9, 14}, {0, 4, 7, 9, 14}, {0, 2, 7, 9, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28793 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom3778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2181 Fin15AnchoredAtom2183 Fin15AnchoredAtom2198
    Fin15AnchoredAtom2283 Fin15AnchoredAtom2568 Fin15AnchoredAtom3778 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 10, 12}, {0, 4, 7, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 4, 10, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28794 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom3779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2181 Fin15AnchoredAtom2184 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2569 Fin15AnchoredAtom3779 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 10, 13}, {0, 4, 7, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28795 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2181 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom3780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2181 Fin15AnchoredAtom2185 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2570 Fin15AnchoredAtom3780 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 10, 14}, {0, 4, 7, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28796 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2182 chi ∧
      Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2201 chi ∧
      Fin15AnchoredAtom2286 chi ∧
      Fin15AnchoredAtom2571 chi ∧
      Fin15AnchoredAtom3781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2182 Fin15AnchoredAtom2183 Fin15AnchoredAtom2201
    Fin15AnchoredAtom2286 Fin15AnchoredAtom2571 Fin15AnchoredAtom3781 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 11, 12}, {0, 4, 7, 11, 12}, {0, 2, 7, 11, 12}, {0, 2, 4, 11, 12}, {0, 2, 4, 7, 12}, {0, 2, 4, 7, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28797 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom3784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2183 Fin15AnchoredAtom2184 Fin15AnchoredAtom2204
    Fin15AnchoredAtom2289 Fin15AnchoredAtom2574 Fin15AnchoredAtom3784 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 12, 13}, {0, 4, 7, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 7, 13}, {0, 2, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28798 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2183 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom3785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2183 Fin15AnchoredAtom2185 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2575 Fin15AnchoredAtom3785 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 12, 14}, {0, 4, 7, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28799 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2184 chi ∧
      Fin15AnchoredAtom2185 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom3786 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2184 Fin15AnchoredAtom2185 Fin15AnchoredAtom2206
    Fin15AnchoredAtom2291 Fin15AnchoredAtom2576 Fin15AnchoredAtom3786 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 7, 13, 14}, {0, 4, 7, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 7, 14}, {0, 2, 4, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
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
