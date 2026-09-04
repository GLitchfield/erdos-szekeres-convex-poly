module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 225. -/

theorem fin15Anchored_clause28800 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2593 chi ∧
      Fin15AnchoredAtom3803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2192 Fin15AnchoredAtom2194 Fin15AnchoredAtom2198
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2593 Fin15AnchoredAtom3803 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 10, 12}, {0, 4, 9, 10, 12}, {0, 2, 9, 10, 12}, {0, 2, 4, 10, 12}, {0, 2, 4, 9, 12}, {0, 2, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28801 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2594 chi ∧
      Fin15AnchoredAtom3804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2192 Fin15AnchoredAtom2195 Fin15AnchoredAtom2199
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2594 Fin15AnchoredAtom3804 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 10, 13}, {0, 4, 9, 10, 13}, {0, 2, 9, 10, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28802 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2192 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2595 chi ∧
      Fin15AnchoredAtom3805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2192 Fin15AnchoredAtom2196 Fin15AnchoredAtom2200
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2595 Fin15AnchoredAtom3805 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 10, 14}, {0, 4, 9, 10, 14}, {0, 2, 9, 10, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28803 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2599 chi ∧
      Fin15AnchoredAtom3809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2194 Fin15AnchoredAtom2195 Fin15AnchoredAtom2204
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2599 Fin15AnchoredAtom3809 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 12, 13}, {0, 4, 9, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 9, 13}, {0, 2, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28804 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2194 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2600 chi ∧
      Fin15AnchoredAtom3810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2194 Fin15AnchoredAtom2196 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2600 Fin15AnchoredAtom3810 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 12, 14}, {0, 4, 9, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28805 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2195 chi ∧
      Fin15AnchoredAtom2196 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2601 chi ∧
      Fin15AnchoredAtom3811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2195 Fin15AnchoredAtom2196 Fin15AnchoredAtom2206
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2601 Fin15AnchoredAtom3811 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 9, 13, 14}, {0, 4, 9, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 9, 14}, {0, 2, 4, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28806 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2605 chi ∧
      Fin15AnchoredAtom3815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2198 Fin15AnchoredAtom2199 Fin15AnchoredAtom2204
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2605 Fin15AnchoredAtom3815 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 10, 12, 13}, {0, 4, 10, 12, 13}, {0, 2, 10, 12, 13}, {0, 2, 4, 12, 13}, {0, 2, 4, 10, 13}, {0, 2, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28807 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2198 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2606 chi ∧
      Fin15AnchoredAtom3816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2198 Fin15AnchoredAtom2200 Fin15AnchoredAtom2205
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2606 Fin15AnchoredAtom3816 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 10, 12, 14}, {0, 4, 10, 12, 14}, {0, 2, 10, 12, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28808 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2199 chi ∧
      Fin15AnchoredAtom2200 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2607 chi ∧
      Fin15AnchoredAtom3817 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2199 Fin15AnchoredAtom2200 Fin15AnchoredAtom2206
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2607 Fin15AnchoredAtom3817 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 10, 13, 14}, {0, 4, 10, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 10, 14}, {0, 2, 4, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28809 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2204 chi ∧
      Fin15AnchoredAtom2205 chi ∧
      Fin15AnchoredAtom2206 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2611 chi ∧
      Fin15AnchoredAtom3821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2204 Fin15AnchoredAtom2205 Fin15AnchoredAtom2206
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2611 Fin15AnchoredAtom3821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 4, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 4, 12, 13, 14}, {0, 4, 12, 13, 14}, {0, 2, 12, 13, 14}, {0, 2, 4, 13, 14}, {0, 2, 4, 12, 14}, {0, 2, 4, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28810 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom3823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2207 Fin15AnchoredAtom2209 Fin15AnchoredAtom2216
    Fin15AnchoredAtom2244 Fin15AnchoredAtom2613 Fin15AnchoredAtom3823 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 9}, {0, 5, 6, 7, 9}, {0, 2, 6, 7, 9}, {0, 2, 5, 7, 9}, {0, 2, 5, 6, 9}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28811 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom3824 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2207 Fin15AnchoredAtom2210 Fin15AnchoredAtom2217
    Fin15AnchoredAtom2245 Fin15AnchoredAtom2614 Fin15AnchoredAtom3824 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 10}, {0, 5, 6, 7, 10}, {0, 2, 6, 7, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28812 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom3826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2207 Fin15AnchoredAtom2212 Fin15AnchoredAtom2219
    Fin15AnchoredAtom2247 Fin15AnchoredAtom2616 Fin15AnchoredAtom3826 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 12}, {0, 5, 6, 7, 12}, {0, 2, 6, 7, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28813 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom3827 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2207 Fin15AnchoredAtom2213 Fin15AnchoredAtom2220
    Fin15AnchoredAtom2248 Fin15AnchoredAtom2617 Fin15AnchoredAtom3827 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 13}, {0, 5, 6, 7, 13}, {0, 2, 6, 7, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28814 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2207 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom3828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2207 Fin15AnchoredAtom2214 Fin15AnchoredAtom2221
    Fin15AnchoredAtom2249 Fin15AnchoredAtom2618 Fin15AnchoredAtom3828 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 7, 14}, {0, 5, 6, 7, 14}, {0, 2, 6, 7, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28815 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom3835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2209 Fin15AnchoredAtom2210 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2256 Fin15AnchoredAtom2625 Fin15AnchoredAtom3835 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 9, 10}, {0, 5, 6, 9, 10}, {0, 2, 6, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 5, 6, 10}, {0, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28816 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom3837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2209 Fin15AnchoredAtom2212 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2258 Fin15AnchoredAtom2627 Fin15AnchoredAtom3837 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 9, 12}, {0, 5, 6, 9, 12}, {0, 2, 6, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28817 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom3838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2209 Fin15AnchoredAtom2213 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2259 Fin15AnchoredAtom2628 Fin15AnchoredAtom3838 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 9, 13}, {0, 5, 6, 9, 13}, {0, 2, 6, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28818 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2209 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom3839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2209 Fin15AnchoredAtom2214 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2260 Fin15AnchoredAtom2629 Fin15AnchoredAtom3839 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 9, 14}, {0, 5, 6, 9, 14}, {0, 2, 6, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28819 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom3841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2210 Fin15AnchoredAtom2212 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2262 Fin15AnchoredAtom2631 Fin15AnchoredAtom3841 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 10, 12}, {0, 5, 6, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 6, 12}, {0, 2, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28820 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom3842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2210 Fin15AnchoredAtom2213 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2263 Fin15AnchoredAtom2632 Fin15AnchoredAtom3842 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 10, 13}, {0, 5, 6, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28821 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2210 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom3843 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2210 Fin15AnchoredAtom2214 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2264 Fin15AnchoredAtom2633 Fin15AnchoredAtom3843 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 10, 14}, {0, 5, 6, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28822 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom3847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2212 Fin15AnchoredAtom2213 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2268 Fin15AnchoredAtom2637 Fin15AnchoredAtom3847 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 12, 13}, {0, 5, 6, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 6, 13}, {0, 2, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28823 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2212 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom3848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2212 Fin15AnchoredAtom2214 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2269 Fin15AnchoredAtom2638 Fin15AnchoredAtom3848 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 12, 14}, {0, 5, 6, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28824 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2213 chi ∧
      Fin15AnchoredAtom2214 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom3849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2213 Fin15AnchoredAtom2214 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2270 Fin15AnchoredAtom2639 Fin15AnchoredAtom3849 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 6, 13, 14}, {0, 5, 6, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 6, 14}, {0, 2, 5, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28825 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom3856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2216 Fin15AnchoredAtom2217 Fin15AnchoredAtom2228
    Fin15AnchoredAtom2277 Fin15AnchoredAtom2646 Fin15AnchoredAtom3856 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 9, 10}, {0, 5, 7, 9, 10}, {0, 2, 7, 9, 10}, {0, 2, 5, 9, 10}, {0, 2, 5, 7, 10}, {0, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28826 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom3858 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2216 Fin15AnchoredAtom2219 Fin15AnchoredAtom2230
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2648 Fin15AnchoredAtom3858 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 9, 12}, {0, 5, 7, 9, 12}, {0, 2, 7, 9, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28827 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom3859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2216 Fin15AnchoredAtom2220 Fin15AnchoredAtom2231
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2649 Fin15AnchoredAtom3859 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 9, 13}, {0, 5, 7, 9, 13}, {0, 2, 7, 9, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28828 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2216 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom3860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2216 Fin15AnchoredAtom2221 Fin15AnchoredAtom2232
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2650 Fin15AnchoredAtom3860 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 9, 14}, {0, 5, 7, 9, 14}, {0, 2, 7, 9, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28829 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom3862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2217 Fin15AnchoredAtom2219 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2283 Fin15AnchoredAtom2652 Fin15AnchoredAtom3862 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 10, 12}, {0, 5, 7, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 7, 12}, {0, 2, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28830 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom3863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2217 Fin15AnchoredAtom2220 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2653 Fin15AnchoredAtom3863 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 10, 13}, {0, 5, 7, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28831 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2217 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom3864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2217 Fin15AnchoredAtom2221 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2654 Fin15AnchoredAtom3864 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 10, 14}, {0, 5, 7, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28832 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom3868 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2219 Fin15AnchoredAtom2220 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2289 Fin15AnchoredAtom2658 Fin15AnchoredAtom3868 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 12, 13}, {0, 5, 7, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 7, 13}, {0, 2, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28833 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2219 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom3869 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2219 Fin15AnchoredAtom2221 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2659 Fin15AnchoredAtom3869 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 12, 14}, {0, 5, 7, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28834 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2220 chi ∧
      Fin15AnchoredAtom2221 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom3870 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2220 Fin15AnchoredAtom2221 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2291 Fin15AnchoredAtom2660 Fin15AnchoredAtom3870 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 7, 13, 14}, {0, 5, 7, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 7, 14}, {0, 2, 5, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28835 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom3887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2228 Fin15AnchoredAtom2230 Fin15AnchoredAtom2234
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2677 Fin15AnchoredAtom3887 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 10, 12}, {0, 5, 9, 10, 12}, {0, 2, 9, 10, 12}, {0, 2, 5, 10, 12}, {0, 2, 5, 9, 12}, {0, 2, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28836 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom3888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2228 Fin15AnchoredAtom2231 Fin15AnchoredAtom2235
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2678 Fin15AnchoredAtom3888 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 10, 13}, {0, 5, 9, 10, 13}, {0, 2, 9, 10, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28837 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2228 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom3889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2228 Fin15AnchoredAtom2232 Fin15AnchoredAtom2236
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2679 Fin15AnchoredAtom3889 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 10, 14}, {0, 5, 9, 10, 14}, {0, 2, 9, 10, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28838 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom3893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2230 Fin15AnchoredAtom2231 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2683 Fin15AnchoredAtom3893 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 12, 13}, {0, 5, 9, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 9, 13}, {0, 2, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28839 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2230 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom3894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2230 Fin15AnchoredAtom2232 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2684 Fin15AnchoredAtom3894 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 12, 14}, {0, 5, 9, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28840 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2231 chi ∧
      Fin15AnchoredAtom2232 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom3895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2231 Fin15AnchoredAtom2232 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2685 Fin15AnchoredAtom3895 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 9, 13, 14}, {0, 5, 9, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 9, 14}, {0, 2, 5, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28841 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2233 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2238 chi ∧
      Fin15AnchoredAtom2318 chi ∧
      Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom3897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2233 Fin15AnchoredAtom2235 Fin15AnchoredAtom2238
    Fin15AnchoredAtom2318 Fin15AnchoredAtom2687 Fin15AnchoredAtom3897 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 10, 11, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 10, 11, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 10, 11, 13}, {0, 5, 10, 11, 13}, {0, 2, 10, 11, 13}, {0, 2, 5, 11, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28842 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2689 chi ∧
      Fin15AnchoredAtom3899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2234 Fin15AnchoredAtom2235 Fin15AnchoredAtom2240
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2689 Fin15AnchoredAtom3899 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 10, 12, 13}, {0, 5, 10, 12, 13}, {0, 2, 10, 12, 13}, {0, 2, 5, 12, 13}, {0, 2, 5, 10, 13}, {0, 2, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28843 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2234 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2690 chi ∧
      Fin15AnchoredAtom3900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2234 Fin15AnchoredAtom2236 Fin15AnchoredAtom2241
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2690 Fin15AnchoredAtom3900 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 10, 12, 14}, {0, 5, 10, 12, 14}, {0, 2, 10, 12, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28844 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2235 chi ∧
      Fin15AnchoredAtom2236 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2691 chi ∧
      Fin15AnchoredAtom3901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2235 Fin15AnchoredAtom2236 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2691 Fin15AnchoredAtom3901 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 10, 13, 14}, {0, 5, 10, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 10, 14}, {0, 2, 5, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28845 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2240 chi ∧
      Fin15AnchoredAtom2241 chi ∧
      Fin15AnchoredAtom2242 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2695 chi ∧
      Fin15AnchoredAtom3905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2240 Fin15AnchoredAtom2241 Fin15AnchoredAtom2242
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2695 Fin15AnchoredAtom3905 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 5, 12, 13, 14}, {0, 5, 12, 13, 14}, {0, 2, 12, 13, 14}, {0, 2, 5, 13, 14}, {0, 2, 5, 12, 14}, {0, 2, 5, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28846 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2702 chi ∧
      Fin15AnchoredAtom3912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2244 Fin15AnchoredAtom2245 Fin15AnchoredAtom2256
    Fin15AnchoredAtom2277 Fin15AnchoredAtom2702 Fin15AnchoredAtom3912 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 9, 10}, {0, 6, 7, 9, 10}, {0, 2, 7, 9, 10}, {0, 2, 6, 9, 10}, {0, 2, 6, 7, 10}, {0, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28847 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2704 chi ∧
      Fin15AnchoredAtom3914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2244 Fin15AnchoredAtom2247 Fin15AnchoredAtom2258
    Fin15AnchoredAtom2279 Fin15AnchoredAtom2704 Fin15AnchoredAtom3914 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 9, 12}, {0, 6, 7, 9, 12}, {0, 2, 7, 9, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28848 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2705 chi ∧
      Fin15AnchoredAtom3915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2244 Fin15AnchoredAtom2248 Fin15AnchoredAtom2259
    Fin15AnchoredAtom2280 Fin15AnchoredAtom2705 Fin15AnchoredAtom3915 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 9, 13}, {0, 6, 7, 9, 13}, {0, 2, 7, 9, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28849 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2244 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2706 chi ∧
      Fin15AnchoredAtom3916 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2244 Fin15AnchoredAtom2249 Fin15AnchoredAtom2260
    Fin15AnchoredAtom2281 Fin15AnchoredAtom2706 Fin15AnchoredAtom3916 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 9, 14}, {0, 6, 7, 9, 14}, {0, 2, 7, 9, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28850 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2708 chi ∧
      Fin15AnchoredAtom3918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2245 Fin15AnchoredAtom2247 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2283 Fin15AnchoredAtom2708 Fin15AnchoredAtom3918 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 10, 12}, {0, 6, 7, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 7, 12}, {0, 2, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28851 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2709 chi ∧
      Fin15AnchoredAtom3919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2245 Fin15AnchoredAtom2248 Fin15AnchoredAtom2263
    Fin15AnchoredAtom2284 Fin15AnchoredAtom2709 Fin15AnchoredAtom3919 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 10, 13}, {0, 6, 7, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28852 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2245 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2710 chi ∧
      Fin15AnchoredAtom3920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2245 Fin15AnchoredAtom2249 Fin15AnchoredAtom2264
    Fin15AnchoredAtom2285 Fin15AnchoredAtom2710 Fin15AnchoredAtom3920 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 10, 14}, {0, 6, 7, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28853 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2714 chi ∧
      Fin15AnchoredAtom3924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2247 Fin15AnchoredAtom2248 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2289 Fin15AnchoredAtom2714 Fin15AnchoredAtom3924 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 12, 13}, {0, 6, 7, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 7, 13}, {0, 2, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28854 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2247 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2715 chi ∧
      Fin15AnchoredAtom3925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2247 Fin15AnchoredAtom2249 Fin15AnchoredAtom2269
    Fin15AnchoredAtom2290 Fin15AnchoredAtom2715 Fin15AnchoredAtom3925 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 12, 14}, {0, 6, 7, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28855 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2248 chi ∧
      Fin15AnchoredAtom2249 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2716 chi ∧
      Fin15AnchoredAtom3926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2248 Fin15AnchoredAtom2249 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2291 Fin15AnchoredAtom2716 Fin15AnchoredAtom3926 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 7, 13, 14}, {0, 6, 7, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 7, 14}, {0, 2, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28856 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2733 chi ∧
      Fin15AnchoredAtom3943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2256 Fin15AnchoredAtom2258 Fin15AnchoredAtom2262
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2733 Fin15AnchoredAtom3943 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 10, 12}, {0, 6, 9, 10, 12}, {0, 2, 9, 10, 12}, {0, 2, 6, 10, 12}, {0, 2, 6, 9, 12}, {0, 2, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28857 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2734 chi ∧
      Fin15AnchoredAtom3944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2256 Fin15AnchoredAtom2259 Fin15AnchoredAtom2263
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2734 Fin15AnchoredAtom3944 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 10, 13}, {0, 6, 9, 10, 13}, {0, 2, 9, 10, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28858 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2256 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2735 chi ∧
      Fin15AnchoredAtom3945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2256 Fin15AnchoredAtom2260 Fin15AnchoredAtom2264
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2735 Fin15AnchoredAtom3945 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 10, 14}, {0, 6, 9, 10, 14}, {0, 2, 9, 10, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28859 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2257 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2267 chi ∧
      Fin15AnchoredAtom2313 chi ∧
      Fin15AnchoredAtom2738 chi ∧
      Fin15AnchoredAtom3948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2257 Fin15AnchoredAtom2260 Fin15AnchoredAtom2267
    Fin15AnchoredAtom2313 Fin15AnchoredAtom2738 Fin15AnchoredAtom3948 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 9, 11, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 9, 11, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 9, 11, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 11, 14}, {0, 6, 9, 11, 14}, {0, 2, 9, 11, 14}, {0, 2, 6, 11, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28860 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2739 chi ∧
      Fin15AnchoredAtom3949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2258 Fin15AnchoredAtom2259 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2739 Fin15AnchoredAtom3949 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 12, 13}, {0, 6, 9, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 9, 13}, {0, 2, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28861 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2258 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2740 chi ∧
      Fin15AnchoredAtom3950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2258 Fin15AnchoredAtom2260 Fin15AnchoredAtom2269
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2740 Fin15AnchoredAtom3950 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 12, 14}, {0, 6, 9, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28862 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2259 chi ∧
      Fin15AnchoredAtom2260 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2741 chi ∧
      Fin15AnchoredAtom3951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2259 Fin15AnchoredAtom2260 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2741 Fin15AnchoredAtom3951 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 9, 13, 14}, {0, 6, 9, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 9, 14}, {0, 2, 6, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28863 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2745 chi ∧
      Fin15AnchoredAtom3955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2262 Fin15AnchoredAtom2263 Fin15AnchoredAtom2268
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2745 Fin15AnchoredAtom3955 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 10, 12, 13}, {0, 6, 10, 12, 13}, {0, 2, 10, 12, 13}, {0, 2, 6, 12, 13}, {0, 2, 6, 10, 13}, {0, 2, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28864 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2262 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2746 chi ∧
      Fin15AnchoredAtom3956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2262 Fin15AnchoredAtom2264 Fin15AnchoredAtom2269
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2746 Fin15AnchoredAtom3956 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 10, 12, 14}, {0, 6, 10, 12, 14}, {0, 2, 10, 12, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28865 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2263 chi ∧
      Fin15AnchoredAtom2264 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2747 chi ∧
      Fin15AnchoredAtom3957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2263 Fin15AnchoredAtom2264 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2747 Fin15AnchoredAtom3957 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 10, 13, 14}, {0, 6, 10, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 10, 14}, {0, 2, 6, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28866 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2268 chi ∧
      Fin15AnchoredAtom2269 chi ∧
      Fin15AnchoredAtom2270 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2751 chi ∧
      Fin15AnchoredAtom3961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2268 Fin15AnchoredAtom2269 Fin15AnchoredAtom2270
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2751 Fin15AnchoredAtom3961 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 6, 12, 13, 14}, {0, 6, 12, 13, 14}, {0, 2, 12, 13, 14}, {0, 2, 6, 13, 14}, {0, 2, 6, 12, 14}, {0, 2, 6, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28867 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2768 chi ∧
      Fin15AnchoredAtom3978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2277 Fin15AnchoredAtom2279 Fin15AnchoredAtom2283
    Fin15AnchoredAtom2308 Fin15AnchoredAtom2768 Fin15AnchoredAtom3978 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 10, 12}, {0, 7, 9, 10, 12}, {0, 2, 9, 10, 12}, {0, 2, 7, 10, 12}, {0, 2, 7, 9, 12}, {0, 2, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28868 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2769 chi ∧
      Fin15AnchoredAtom3979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2277 Fin15AnchoredAtom2280 Fin15AnchoredAtom2284
    Fin15AnchoredAtom2309 Fin15AnchoredAtom2769 Fin15AnchoredAtom3979 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 10, 13}, {0, 7, 9, 10, 13}, {0, 2, 9, 10, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28869 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2277 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2770 chi ∧
      Fin15AnchoredAtom3980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2277 Fin15AnchoredAtom2281 Fin15AnchoredAtom2285
    Fin15AnchoredAtom2310 Fin15AnchoredAtom2770 Fin15AnchoredAtom3980 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 10, 14}, {0, 7, 9, 10, 14}, {0, 2, 9, 10, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28870 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2774 chi ∧
      Fin15AnchoredAtom3984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2279 Fin15AnchoredAtom2280 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2314 Fin15AnchoredAtom2774 Fin15AnchoredAtom3984 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 12, 13}, {0, 7, 9, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 9, 13}, {0, 2, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28871 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2279 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2775 chi ∧
      Fin15AnchoredAtom3985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2279 Fin15AnchoredAtom2281 Fin15AnchoredAtom2290
    Fin15AnchoredAtom2315 Fin15AnchoredAtom2775 Fin15AnchoredAtom3985 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 12, 14}, {0, 7, 9, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28872 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2280 chi ∧
      Fin15AnchoredAtom2281 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2776 chi ∧
      Fin15AnchoredAtom3986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2280 Fin15AnchoredAtom2281 Fin15AnchoredAtom2291
    Fin15AnchoredAtom2316 Fin15AnchoredAtom2776 Fin15AnchoredAtom3986 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 9, 13, 14}, {0, 7, 9, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 9, 14}, {0, 2, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28873 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2780 chi ∧
      Fin15AnchoredAtom3990 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2283 Fin15AnchoredAtom2284 Fin15AnchoredAtom2289
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2780 Fin15AnchoredAtom3990 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 10, 12, 13}, {0, 7, 10, 12, 13}, {0, 2, 10, 12, 13}, {0, 2, 7, 12, 13}, {0, 2, 7, 10, 13}, {0, 2, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28874 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2283 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2781 chi ∧
      Fin15AnchoredAtom3991 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2283 Fin15AnchoredAtom2285 Fin15AnchoredAtom2290
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2781 Fin15AnchoredAtom3991 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 10, 12, 14}, {0, 7, 10, 12, 14}, {0, 2, 10, 12, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28875 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2284 chi ∧
      Fin15AnchoredAtom2285 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2782 chi ∧
      Fin15AnchoredAtom3992 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2284 Fin15AnchoredAtom2285 Fin15AnchoredAtom2291
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2782 Fin15AnchoredAtom3992 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 10, 13, 14}, {0, 7, 10, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 10, 14}, {0, 2, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28876 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2289 chi ∧
      Fin15AnchoredAtom2290 chi ∧
      Fin15AnchoredAtom2291 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2786 chi ∧
      Fin15AnchoredAtom3996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2289 Fin15AnchoredAtom2290 Fin15AnchoredAtom2291
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2786 Fin15AnchoredAtom3996 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 7, 12, 13, 14}, {0, 7, 12, 13, 14}, {0, 2, 12, 13, 14}, {0, 2, 7, 13, 14}, {0, 2, 7, 12, 14}, {0, 2, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28877 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2810 chi ∧
      Fin15AnchoredAtom4020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2308 Fin15AnchoredAtom2309 Fin15AnchoredAtom2314
    Fin15AnchoredAtom2320 Fin15AnchoredAtom2810 Fin15AnchoredAtom4020 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 9, 10, 12, 13}, {0, 9, 10, 12, 13}, {0, 2, 10, 12, 13}, {0, 2, 9, 12, 13}, {0, 2, 9, 10, 13}, {0, 2, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28878 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2308 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2811 chi ∧
      Fin15AnchoredAtom4021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2308 Fin15AnchoredAtom2310 Fin15AnchoredAtom2315
    Fin15AnchoredAtom2321 Fin15AnchoredAtom2811 Fin15AnchoredAtom4021 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 9, 10, 12, 14}, {0, 9, 10, 12, 14}, {0, 2, 10, 12, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28879 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2309 chi ∧
      Fin15AnchoredAtom2310 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2812 chi ∧
      Fin15AnchoredAtom4022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2309 Fin15AnchoredAtom2310 Fin15AnchoredAtom2316
    Fin15AnchoredAtom2322 Fin15AnchoredAtom2812 Fin15AnchoredAtom4022 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 9, 10, 13, 14}, {0, 9, 10, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 10, 14}, {0, 2, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28880 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2314 chi ∧
      Fin15AnchoredAtom2315 chi ∧
      Fin15AnchoredAtom2316 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2816 chi ∧
      Fin15AnchoredAtom4026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2314 Fin15AnchoredAtom2315 Fin15AnchoredAtom2316
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2816 Fin15AnchoredAtom4026 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 9, 12, 13, 14}, {0, 9, 12, 13, 14}, {0, 2, 12, 13, 14}, {0, 2, 9, 13, 14}, {0, 2, 9, 12, 14}, {0, 2, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28881 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2320 chi ∧
      Fin15AnchoredAtom2321 chi ∧
      Fin15AnchoredAtom2322 chi ∧
      Fin15AnchoredAtom2326 chi ∧
      Fin15AnchoredAtom2820 chi ∧
      Fin15AnchoredAtom4030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2320 Fin15AnchoredAtom2321 Fin15AnchoredAtom2322
    Fin15AnchoredAtom2326 Fin15AnchoredAtom2820 Fin15AnchoredAtom4030 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 2, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 2, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 2, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{2, 10, 12, 13, 14}, {0, 10, 12, 13, 14}, {0, 2, 12, 13, 14}, {0, 2, 10, 13, 14}, {0, 2, 10, 12, 14}, {0, 2, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28882 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2372 chi ∧
      Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom4032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2327 Fin15AnchoredAtom2328 Fin15AnchoredAtom2336
    Fin15AnchoredAtom2372 Fin15AnchoredAtom2492 Fin15AnchoredAtom4032 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 7}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 6, 7} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 7}, {0, 4, 5, 6, 7}, {0, 3, 5, 6, 7}, {0, 3, 4, 6, 7}, {0, 3, 4, 5, 7}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28883 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2373 chi ∧
      Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom4033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2327 Fin15AnchoredAtom2329 Fin15AnchoredAtom2337
    Fin15AnchoredAtom2373 Fin15AnchoredAtom2493 Fin15AnchoredAtom4033 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 6, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 6, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 8}, {0, 4, 5, 6, 8}, {0, 3, 5, 6, 8}, {0, 3, 4, 6, 8}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28884 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2374 chi ∧
      Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom4034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2327 Fin15AnchoredAtom2330 Fin15AnchoredAtom2338
    Fin15AnchoredAtom2374 Fin15AnchoredAtom2494 Fin15AnchoredAtom4034 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 6, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 9}, {0, 4, 5, 6, 9}, {0, 3, 5, 6, 9}, {0, 3, 4, 6, 9}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28885 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2375 chi ∧
      Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom4035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2327 Fin15AnchoredAtom2331 Fin15AnchoredAtom2339
    Fin15AnchoredAtom2375 Fin15AnchoredAtom2495 Fin15AnchoredAtom4035 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 6, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 10}, {0, 4, 5, 6, 10}, {0, 3, 5, 6, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28886 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2332 chi ∧
      Fin15AnchoredAtom2340 chi ∧
      Fin15AnchoredAtom2376 chi ∧
      Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom4036 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2327 Fin15AnchoredAtom2332 Fin15AnchoredAtom2340
    Fin15AnchoredAtom2376 Fin15AnchoredAtom2496 Fin15AnchoredAtom4036 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 6, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 6, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 11}, {0, 4, 5, 6, 11}, {0, 3, 5, 6, 11}, {0, 3, 4, 6, 11}, {0, 3, 4, 5, 11}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28887 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2377 chi ∧
      Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom4037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2327 Fin15AnchoredAtom2333 Fin15AnchoredAtom2341
    Fin15AnchoredAtom2377 Fin15AnchoredAtom2497 Fin15AnchoredAtom4037 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 6, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 12}, {0, 4, 5, 6, 12}, {0, 3, 5, 6, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28888 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2378 chi ∧
      Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom4038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2327 Fin15AnchoredAtom2334 Fin15AnchoredAtom2342
    Fin15AnchoredAtom2378 Fin15AnchoredAtom2498 Fin15AnchoredAtom4038 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 6, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 13}, {0, 4, 5, 6, 13}, {0, 3, 5, 6, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28889 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2327 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2379 chi ∧
      Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom4039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2327 Fin15AnchoredAtom2335 Fin15AnchoredAtom2343
    Fin15AnchoredAtom2379 Fin15AnchoredAtom2499 Fin15AnchoredAtom4039 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 6, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 6, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 6, 14}, {0, 4, 5, 6, 14}, {0, 3, 5, 6, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 6}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28890 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2380 chi ∧
      Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom4040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2328 Fin15AnchoredAtom2329 Fin15AnchoredAtom2344
    Fin15AnchoredAtom2380 Fin15AnchoredAtom2500 Fin15AnchoredAtom4040 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 8}, {0, 4, 5, 7, 8}, {0, 3, 5, 7, 8}, {0, 3, 4, 7, 8}, {0, 3, 4, 5, 8}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28891 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2381 chi ∧
      Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom4041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2328 Fin15AnchoredAtom2330 Fin15AnchoredAtom2345
    Fin15AnchoredAtom2381 Fin15AnchoredAtom2501 Fin15AnchoredAtom4041 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 9}, {0, 4, 5, 7, 9}, {0, 3, 5, 7, 9}, {0, 3, 4, 7, 9}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28892 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2382 chi ∧
      Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom4042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2328 Fin15AnchoredAtom2331 Fin15AnchoredAtom2346
    Fin15AnchoredAtom2382 Fin15AnchoredAtom2502 Fin15AnchoredAtom4042 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 10}, {0, 4, 5, 7, 10}, {0, 3, 5, 7, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28893 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2384 chi ∧
      Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom4044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2328 Fin15AnchoredAtom2333 Fin15AnchoredAtom2348
    Fin15AnchoredAtom2384 Fin15AnchoredAtom2504 Fin15AnchoredAtom4044 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 12}, {0, 4, 5, 7, 12}, {0, 3, 5, 7, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28894 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2385 chi ∧
      Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom4045 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2328 Fin15AnchoredAtom2334 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2385 Fin15AnchoredAtom2505 Fin15AnchoredAtom4045 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 13}, {0, 4, 5, 7, 13}, {0, 3, 5, 7, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28895 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2328 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2386 chi ∧
      Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom4046 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2328 Fin15AnchoredAtom2335 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2386 Fin15AnchoredAtom2506 Fin15AnchoredAtom4046 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 7, 14}, {0, 4, 5, 7, 14}, {0, 3, 5, 7, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28896 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2387 chi ∧
      Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom4047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2329 Fin15AnchoredAtom2330 Fin15AnchoredAtom2351
    Fin15AnchoredAtom2387 Fin15AnchoredAtom2507 Fin15AnchoredAtom4047 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 8, 9}, {0, 4, 5, 8, 9}, {0, 3, 5, 8, 9}, {0, 3, 4, 8, 9}, {0, 3, 4, 5, 9}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28897 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2388 chi ∧
      Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom4048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2329 Fin15AnchoredAtom2331 Fin15AnchoredAtom2352
    Fin15AnchoredAtom2388 Fin15AnchoredAtom2508 Fin15AnchoredAtom4048 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 8, 10}, {0, 4, 5, 8, 10}, {0, 3, 5, 8, 10}, {0, 3, 4, 8, 10}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28898 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2390 chi ∧
      Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom4050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2329 Fin15AnchoredAtom2333 Fin15AnchoredAtom2354
    Fin15AnchoredAtom2390 Fin15AnchoredAtom2510 Fin15AnchoredAtom4050 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 8, 12}, {0, 4, 5, 8, 12}, {0, 3, 5, 8, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28899 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2391 chi ∧
      Fin15AnchoredAtom2511 chi ∧
      Fin15AnchoredAtom4051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2329 Fin15AnchoredAtom2334 Fin15AnchoredAtom2355
    Fin15AnchoredAtom2391 Fin15AnchoredAtom2511 Fin15AnchoredAtom4051 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 8, 13}, {0, 4, 5, 8, 13}, {0, 3, 5, 8, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28900 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2329 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2392 chi ∧
      Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom4052 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2329 Fin15AnchoredAtom2335 Fin15AnchoredAtom2356
    Fin15AnchoredAtom2392 Fin15AnchoredAtom2512 Fin15AnchoredAtom4052 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 8, 14}, {0, 4, 5, 8, 14}, {0, 3, 5, 8, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28901 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2393 chi ∧
      Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom4053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2330 Fin15AnchoredAtom2331 Fin15AnchoredAtom2357
    Fin15AnchoredAtom2393 Fin15AnchoredAtom2513 Fin15AnchoredAtom4053 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 10}, {0, 4, 5, 9, 10}, {0, 3, 5, 9, 10}, {0, 3, 4, 9, 10}, {0, 3, 4, 5, 10}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28902 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2332 chi ∧
      Fin15AnchoredAtom2358 chi ∧
      Fin15AnchoredAtom2394 chi ∧
      Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom4054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2330 Fin15AnchoredAtom2332 Fin15AnchoredAtom2358
    Fin15AnchoredAtom2394 Fin15AnchoredAtom2514 Fin15AnchoredAtom4054 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 9, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 9, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 9, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 11}, {0, 4, 5, 9, 11}, {0, 3, 5, 9, 11}, {0, 3, 4, 9, 11}, {0, 3, 4, 5, 11}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28903 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2395 chi ∧
      Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom4055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2330 Fin15AnchoredAtom2333 Fin15AnchoredAtom2359
    Fin15AnchoredAtom2395 Fin15AnchoredAtom2515 Fin15AnchoredAtom4055 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 12}, {0, 4, 5, 9, 12}, {0, 3, 5, 9, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28904 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2396 chi ∧
      Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom4056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2330 Fin15AnchoredAtom2334 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2396 Fin15AnchoredAtom2516 Fin15AnchoredAtom4056 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 13}, {0, 4, 5, 9, 13}, {0, 3, 5, 9, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28905 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2330 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2397 chi ∧
      Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom4057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2330 Fin15AnchoredAtom2335 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2397 Fin15AnchoredAtom2517 Fin15AnchoredAtom4057 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 9, 14}, {0, 4, 5, 9, 14}, {0, 3, 5, 9, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28906 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2399 chi ∧
      Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom4059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2331 Fin15AnchoredAtom2333 Fin15AnchoredAtom2363
    Fin15AnchoredAtom2399 Fin15AnchoredAtom2519 Fin15AnchoredAtom4059 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 12}, {0, 4, 5, 10, 12}, {0, 3, 5, 10, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 5, 12}, {0, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28907 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2364 chi ∧
      Fin15AnchoredAtom2400 chi ∧
      Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom4060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2331 Fin15AnchoredAtom2334 Fin15AnchoredAtom2364
    Fin15AnchoredAtom2400 Fin15AnchoredAtom2520 Fin15AnchoredAtom4060 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 13}, {0, 4, 5, 10, 13}, {0, 3, 5, 10, 13}, {0, 3, 4, 10, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28908 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2331 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2365 chi ∧
      Fin15AnchoredAtom2401 chi ∧
      Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom4061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2331 Fin15AnchoredAtom2335 Fin15AnchoredAtom2365
    Fin15AnchoredAtom2401 Fin15AnchoredAtom2521 Fin15AnchoredAtom4061 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 14}, {0, 4, 5, 10, 14}, {0, 3, 5, 10, 14}, {0, 3, 4, 10, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28909 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2369 chi ∧
      Fin15AnchoredAtom2405 chi ∧
      Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom4065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2333 Fin15AnchoredAtom2334 Fin15AnchoredAtom2369
    Fin15AnchoredAtom2405 Fin15AnchoredAtom2525 Fin15AnchoredAtom4065 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 12, 13}, {0, 4, 5, 12, 13}, {0, 3, 5, 12, 13}, {0, 3, 4, 12, 13}, {0, 3, 4, 5, 13}, {0, 3, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28910 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2333 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2370 chi ∧
      Fin15AnchoredAtom2406 chi ∧
      Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom4066 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2333 Fin15AnchoredAtom2335 Fin15AnchoredAtom2370
    Fin15AnchoredAtom2406 Fin15AnchoredAtom2526 Fin15AnchoredAtom4066 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 12, 14}, {0, 4, 5, 12, 14}, {0, 3, 5, 12, 14}, {0, 3, 4, 12, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28911 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2334 chi ∧
      Fin15AnchoredAtom2335 chi ∧
      Fin15AnchoredAtom2371 chi ∧
      Fin15AnchoredAtom2407 chi ∧
      Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom4067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2334 Fin15AnchoredAtom2335 Fin15AnchoredAtom2371
    Fin15AnchoredAtom2407 Fin15AnchoredAtom2527 Fin15AnchoredAtom4067 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 13, 14}, {0, 4, 5, 13, 14}, {0, 3, 5, 13, 14}, {0, 3, 4, 13, 14}, {0, 3, 4, 5, 14}, {0, 3, 4, 5, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28912 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2344 chi ∧
      Fin15AnchoredAtom2408 chi ∧
      Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom4068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2336 Fin15AnchoredAtom2337 Fin15AnchoredAtom2344
    Fin15AnchoredAtom2408 Fin15AnchoredAtom2528 Fin15AnchoredAtom4068 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 8}, {0, 4, 6, 7, 8}, {0, 3, 6, 7, 8}, {0, 3, 4, 7, 8}, {0, 3, 4, 6, 8}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28913 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2345 chi ∧
      Fin15AnchoredAtom2409 chi ∧
      Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom4069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2336 Fin15AnchoredAtom2338 Fin15AnchoredAtom2345
    Fin15AnchoredAtom2409 Fin15AnchoredAtom2529 Fin15AnchoredAtom4069 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 9}, {0, 4, 6, 7, 9}, {0, 3, 6, 7, 9}, {0, 3, 4, 7, 9}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28914 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2346 chi ∧
      Fin15AnchoredAtom2410 chi ∧
      Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom4070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2336 Fin15AnchoredAtom2339 Fin15AnchoredAtom2346
    Fin15AnchoredAtom2410 Fin15AnchoredAtom2530 Fin15AnchoredAtom4070 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 10}, {0, 4, 6, 7, 10}, {0, 3, 6, 7, 10}, {0, 3, 4, 7, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28915 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2348 chi ∧
      Fin15AnchoredAtom2412 chi ∧
      Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom4072 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2336 Fin15AnchoredAtom2341 Fin15AnchoredAtom2348
    Fin15AnchoredAtom2412 Fin15AnchoredAtom2532 Fin15AnchoredAtom4072 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 12}, {0, 4, 6, 7, 12}, {0, 3, 6, 7, 12}, {0, 3, 4, 7, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28916 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2349 chi ∧
      Fin15AnchoredAtom2413 chi ∧
      Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom4073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2336 Fin15AnchoredAtom2342 Fin15AnchoredAtom2349
    Fin15AnchoredAtom2413 Fin15AnchoredAtom2533 Fin15AnchoredAtom4073 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 13}, {0, 4, 6, 7, 13}, {0, 3, 6, 7, 13}, {0, 3, 4, 7, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28917 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2336 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2350 chi ∧
      Fin15AnchoredAtom2414 chi ∧
      Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom4074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2336 Fin15AnchoredAtom2343 Fin15AnchoredAtom2350
    Fin15AnchoredAtom2414 Fin15AnchoredAtom2534 Fin15AnchoredAtom4074 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 14}, {0, 4, 6, 7, 14}, {0, 3, 6, 7, 14}, {0, 3, 4, 7, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28918 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2351 chi ∧
      Fin15AnchoredAtom2415 chi ∧
      Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom4075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2337 Fin15AnchoredAtom2338 Fin15AnchoredAtom2351
    Fin15AnchoredAtom2415 Fin15AnchoredAtom2535 Fin15AnchoredAtom4075 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 8, 9}, {0, 4, 6, 8, 9}, {0, 3, 6, 8, 9}, {0, 3, 4, 8, 9}, {0, 3, 4, 6, 9}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28919 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2352 chi ∧
      Fin15AnchoredAtom2416 chi ∧
      Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom4076 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2337 Fin15AnchoredAtom2339 Fin15AnchoredAtom2352
    Fin15AnchoredAtom2416 Fin15AnchoredAtom2536 Fin15AnchoredAtom4076 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 8, 10}, {0, 4, 6, 8, 10}, {0, 3, 6, 8, 10}, {0, 3, 4, 8, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28920 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2354 chi ∧
      Fin15AnchoredAtom2418 chi ∧
      Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom4078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2337 Fin15AnchoredAtom2341 Fin15AnchoredAtom2354
    Fin15AnchoredAtom2418 Fin15AnchoredAtom2538 Fin15AnchoredAtom4078 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 8, 12}, {0, 4, 6, 8, 12}, {0, 3, 6, 8, 12}, {0, 3, 4, 8, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28921 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2355 chi ∧
      Fin15AnchoredAtom2419 chi ∧
      Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom4079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2337 Fin15AnchoredAtom2342 Fin15AnchoredAtom2355
    Fin15AnchoredAtom2419 Fin15AnchoredAtom2539 Fin15AnchoredAtom4079 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 8, 13}, {0, 4, 6, 8, 13}, {0, 3, 6, 8, 13}, {0, 3, 4, 8, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28922 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2337 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2356 chi ∧
      Fin15AnchoredAtom2420 chi ∧
      Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom4080 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2337 Fin15AnchoredAtom2343 Fin15AnchoredAtom2356
    Fin15AnchoredAtom2420 Fin15AnchoredAtom2540 Fin15AnchoredAtom4080 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 8, 14}, {0, 4, 6, 8, 14}, {0, 3, 6, 8, 14}, {0, 3, 4, 8, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28923 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2357 chi ∧
      Fin15AnchoredAtom2421 chi ∧
      Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom4081 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2338 Fin15AnchoredAtom2339 Fin15AnchoredAtom2357
    Fin15AnchoredAtom2421 Fin15AnchoredAtom2541 Fin15AnchoredAtom4081 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 10}, {0, 4, 6, 9, 10}, {0, 3, 6, 9, 10}, {0, 3, 4, 9, 10}, {0, 3, 4, 6, 10}, {0, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28924 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2359 chi ∧
      Fin15AnchoredAtom2423 chi ∧
      Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom4083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2338 Fin15AnchoredAtom2341 Fin15AnchoredAtom2359
    Fin15AnchoredAtom2423 Fin15AnchoredAtom2543 Fin15AnchoredAtom4083 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 12}, {0, 4, 6, 9, 12}, {0, 3, 6, 9, 12}, {0, 3, 4, 9, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28925 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2342 chi ∧
      Fin15AnchoredAtom2360 chi ∧
      Fin15AnchoredAtom2424 chi ∧
      Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom4084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2338 Fin15AnchoredAtom2342 Fin15AnchoredAtom2360
    Fin15AnchoredAtom2424 Fin15AnchoredAtom2544 Fin15AnchoredAtom4084 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 13}, {0, 4, 6, 9, 13}, {0, 3, 6, 9, 13}, {0, 3, 4, 9, 13}, {0, 3, 4, 6, 13}, {0, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28926 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2338 chi ∧
      Fin15AnchoredAtom2343 chi ∧
      Fin15AnchoredAtom2361 chi ∧
      Fin15AnchoredAtom2425 chi ∧
      Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom4085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2338 Fin15AnchoredAtom2343 Fin15AnchoredAtom2361
    Fin15AnchoredAtom2425 Fin15AnchoredAtom2545 Fin15AnchoredAtom4085 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 14}, {0, 4, 6, 9, 14}, {0, 3, 6, 9, 14}, {0, 3, 4, 9, 14}, {0, 3, 4, 6, 14}, {0, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause28927 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom2339 chi ∧
      Fin15AnchoredAtom2341 chi ∧
      Fin15AnchoredAtom2363 chi ∧
      Fin15AnchoredAtom2427 chi ∧
      Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom4087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom2339 Fin15AnchoredAtom2341 Fin15AnchoredAtom2363
    Fin15AnchoredAtom2427 Fin15AnchoredAtom2547 Fin15AnchoredAtom4087 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{0, 3, 4, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({0, 3, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({0, 3, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 12}, {0, 4, 6, 10, 12}, {0, 3, 6, 10, 12}, {0, 3, 4, 10, 12}, {0, 3, 4, 6, 12}, {0, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
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
