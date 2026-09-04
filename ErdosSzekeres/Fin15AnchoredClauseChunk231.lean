module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 231. -/

theorem fin15Anchored_clause29568 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3046 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom4061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3046 Fin15AnchoredAtom3050 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3116 Fin15AnchoredAtom3236 Fin15AnchoredAtom4061 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 10, 14}, {1, 4, 5, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29569 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom4065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3048 Fin15AnchoredAtom3049 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3120 Fin15AnchoredAtom3240 Fin15AnchoredAtom4065 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 12, 13}, {1, 4, 5, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 5, 13}, {1, 3, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29570 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3048 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom4066 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3048 Fin15AnchoredAtom3050 Fin15AnchoredAtom3085
    Fin15AnchoredAtom3121 Fin15AnchoredAtom3241 Fin15AnchoredAtom4066 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 12, 14}, {1, 4, 5, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29571 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3049 chi ∧
      Fin15AnchoredAtom3050 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom4067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3049 Fin15AnchoredAtom3050 Fin15AnchoredAtom3086
    Fin15AnchoredAtom3122 Fin15AnchoredAtom3242 Fin15AnchoredAtom4067 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 5, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 5, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 5, 13, 14}, {1, 4, 5, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 5, 14}, {1, 3, 4, 5, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29572 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom3243 chi ∧
      Fin15AnchoredAtom4068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3052 Fin15AnchoredAtom3059
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3243 Fin15AnchoredAtom4068 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 8}, {1, 4, 6, 7, 8}, {1, 3, 6, 7, 8}, {1, 3, 4, 7, 8}, {1, 3, 4, 6, 8}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29573 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom4069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3053 Fin15AnchoredAtom3060
    Fin15AnchoredAtom3124 Fin15AnchoredAtom3244 Fin15AnchoredAtom4069 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 9}, {1, 4, 6, 7, 9}, {1, 3, 6, 7, 9}, {1, 3, 4, 7, 9}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29574 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom4070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3054 Fin15AnchoredAtom3061
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3245 Fin15AnchoredAtom4070 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 10}, {1, 4, 6, 7, 10}, {1, 3, 6, 7, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29575 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom4072 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3056 Fin15AnchoredAtom3063
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3247 Fin15AnchoredAtom4072 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 12}, {1, 4, 6, 7, 12}, {1, 3, 6, 7, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29576 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom4073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3057 Fin15AnchoredAtom3064
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3248 Fin15AnchoredAtom4073 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 13}, {1, 4, 6, 7, 13}, {1, 3, 6, 7, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29577 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3051 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom4074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3051 Fin15AnchoredAtom3058 Fin15AnchoredAtom3065
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3249 Fin15AnchoredAtom4074 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 7, 14}, {1, 4, 6, 7, 14}, {1, 3, 6, 7, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29578 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom4075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3052 Fin15AnchoredAtom3053 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3130 Fin15AnchoredAtom3250 Fin15AnchoredAtom4075 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 8, 9}, {1, 4, 6, 8, 9}, {1, 3, 6, 8, 9}, {1, 3, 4, 8, 9}, {1, 3, 4, 6, 9}, {1, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29579 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3131 chi ∧
      Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom4076 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3052 Fin15AnchoredAtom3054 Fin15AnchoredAtom3067
    Fin15AnchoredAtom3131 Fin15AnchoredAtom3251 Fin15AnchoredAtom4076 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 8, 10}, {1, 4, 6, 8, 10}, {1, 3, 6, 8, 10}, {1, 3, 4, 8, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29580 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3052 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom4079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3052 Fin15AnchoredAtom3057 Fin15AnchoredAtom3070
    Fin15AnchoredAtom3134 Fin15AnchoredAtom3254 Fin15AnchoredAtom4079 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 8, 13}, {1, 4, 6, 8, 13}, {1, 3, 6, 8, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29581 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom4081 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3053 Fin15AnchoredAtom3054 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3256 Fin15AnchoredAtom4081 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 10}, {1, 4, 6, 9, 10}, {1, 3, 6, 9, 10}, {1, 3, 4, 9, 10}, {1, 3, 4, 6, 10}, {1, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29582 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom4083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3053 Fin15AnchoredAtom3056 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3258 Fin15AnchoredAtom4083 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 12}, {1, 4, 6, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29583 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom4084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3053 Fin15AnchoredAtom3057 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3259 Fin15AnchoredAtom4084 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 13}, {1, 4, 6, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29584 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3053 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom4085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3053 Fin15AnchoredAtom3058 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3260 Fin15AnchoredAtom4085 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 9, 14}, {1, 4, 6, 9, 14}, {1, 3, 6, 9, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29585 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom4087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3054 Fin15AnchoredAtom3056 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3262 Fin15AnchoredAtom4087 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 12}, {1, 4, 6, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 6, 12}, {1, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29586 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom4088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3054 Fin15AnchoredAtom3057 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3263 Fin15AnchoredAtom4088 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 13}, {1, 4, 6, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29587 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3054 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom4089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3054 Fin15AnchoredAtom3058 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3264 Fin15AnchoredAtom4089 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 10, 14}, {1, 4, 6, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29588 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom4093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3056 Fin15AnchoredAtom3057 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3268 Fin15AnchoredAtom4093 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 12, 13}, {1, 4, 6, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 6, 13}, {1, 3, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29589 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3056 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom4094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3056 Fin15AnchoredAtom3058 Fin15AnchoredAtom3085
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3269 Fin15AnchoredAtom4094 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 12, 14}, {1, 4, 6, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29590 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3057 chi ∧
      Fin15AnchoredAtom3058 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom4095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3057 Fin15AnchoredAtom3058 Fin15AnchoredAtom3086
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3270 Fin15AnchoredAtom4095 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 6, 13, 14}, {1, 4, 6, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 6, 14}, {1, 3, 4, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29591 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom3271 chi ∧
      Fin15AnchoredAtom4096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3059 Fin15AnchoredAtom3060 Fin15AnchoredAtom3066
    Fin15AnchoredAtom3151 Fin15AnchoredAtom3271 Fin15AnchoredAtom4096 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 8, 9}, {1, 4, 7, 8, 9}, {1, 3, 7, 8, 9}, {1, 3, 4, 8, 9}, {1, 3, 4, 7, 9}, {1, 3, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29592 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom3272 chi ∧
      Fin15AnchoredAtom4097 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3059 Fin15AnchoredAtom3061 Fin15AnchoredAtom3067
    Fin15AnchoredAtom3152 Fin15AnchoredAtom3272 Fin15AnchoredAtom4097 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 8, 10}, {1, 4, 7, 8, 10}, {1, 3, 7, 8, 10}, {1, 3, 4, 8, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29593 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom3274 chi ∧
      Fin15AnchoredAtom4099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3059 Fin15AnchoredAtom3063 Fin15AnchoredAtom3069
    Fin15AnchoredAtom3154 Fin15AnchoredAtom3274 Fin15AnchoredAtom4099 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 8, 12}, {1, 4, 7, 8, 12}, {1, 3, 7, 8, 12}, {1, 3, 4, 8, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29594 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3059 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3275 chi ∧
      Fin15AnchoredAtom4100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3059 Fin15AnchoredAtom3064 Fin15AnchoredAtom3070
    Fin15AnchoredAtom3155 Fin15AnchoredAtom3275 Fin15AnchoredAtom4100 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 8, 13}, {1, 4, 7, 8, 13}, {1, 3, 7, 8, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29595 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom4102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3060 Fin15AnchoredAtom3061 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3277 Fin15AnchoredAtom4102 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 4, 9, 10}, {1, 3, 4, 7, 10}, {1, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29596 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom4104 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3060 Fin15AnchoredAtom3063 Fin15AnchoredAtom3074
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3279 Fin15AnchoredAtom4104 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 3, 7, 9, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29597 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom4105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3060 Fin15AnchoredAtom3064 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3280 Fin15AnchoredAtom4105 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 3, 7, 9, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29598 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3060 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom4106 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3060 Fin15AnchoredAtom3065 Fin15AnchoredAtom3076
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3281 Fin15AnchoredAtom4106 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 3, 7, 9, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29599 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom4108 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3061 Fin15AnchoredAtom3063 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3283 Fin15AnchoredAtom4108 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29600 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom4109 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3061 Fin15AnchoredAtom3064 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3284 Fin15AnchoredAtom4109 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29601 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3061 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom4110 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3061 Fin15AnchoredAtom3065 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3285 Fin15AnchoredAtom4110 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29602 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3062 chi ∧
      Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3081 chi ∧
      Fin15AnchoredAtom3166 chi ∧
      Fin15AnchoredAtom3286 chi ∧
      Fin15AnchoredAtom4111 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3062 Fin15AnchoredAtom3063 Fin15AnchoredAtom3081
    Fin15AnchoredAtom3166 Fin15AnchoredAtom3286 Fin15AnchoredAtom4111 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 11, 12}, {1, 4, 7, 11, 12}, {1, 3, 7, 11, 12}, {1, 3, 4, 11, 12}, {1, 3, 4, 7, 12}, {1, 3, 4, 7, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29603 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom4114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3063 Fin15AnchoredAtom3064 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3289 Fin15AnchoredAtom4114 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 12, 13}, {1, 4, 7, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 7, 13}, {1, 3, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29604 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3063 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom4115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3063 Fin15AnchoredAtom3065 Fin15AnchoredAtom3085
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3290 Fin15AnchoredAtom4115 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 12, 14}, {1, 4, 7, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29605 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3064 chi ∧
      Fin15AnchoredAtom3065 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom4116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3064 Fin15AnchoredAtom3065 Fin15AnchoredAtom3086
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3291 Fin15AnchoredAtom4116 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 7, 13, 14}, {1, 4, 7, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 7, 14}, {1, 3, 4, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29606 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom4117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3066 Fin15AnchoredAtom3067 Fin15AnchoredAtom3072
    Fin15AnchoredAtom3172 Fin15AnchoredAtom3292 Fin15AnchoredAtom4117 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 9, 10}, {1, 4, 8, 9, 10}, {1, 3, 8, 9, 10}, {1, 3, 4, 9, 10}, {1, 3, 4, 8, 10}, {1, 3, 4, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29607 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3066 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom4120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3066 Fin15AnchoredAtom3070 Fin15AnchoredAtom3075
    Fin15AnchoredAtom3175 Fin15AnchoredAtom3295 Fin15AnchoredAtom4120 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 9, 13}, {1, 4, 8, 9, 13}, {1, 3, 8, 9, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29608 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom3298 chi ∧
      Fin15AnchoredAtom4123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3067 Fin15AnchoredAtom3069 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3178 Fin15AnchoredAtom3298 Fin15AnchoredAtom4123 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 10, 12}, {1, 4, 8, 10, 12}, {1, 3, 8, 10, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 8, 12}, {1, 3, 4, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29609 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3067 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom4124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3067 Fin15AnchoredAtom3070 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3179 Fin15AnchoredAtom3299 Fin15AnchoredAtom4124 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 10, 13}, {1, 4, 8, 10, 13}, {1, 3, 8, 10, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29610 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom4129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3069 Fin15AnchoredAtom3070 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3184 Fin15AnchoredAtom3304 Fin15AnchoredAtom4129 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 12, 13}, {1, 4, 8, 12, 13}, {1, 3, 8, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 8, 13}, {1, 3, 4, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29611 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3069 chi ∧
      Fin15AnchoredAtom3071 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3185 chi ∧
      Fin15AnchoredAtom3305 chi ∧
      Fin15AnchoredAtom4130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3069 Fin15AnchoredAtom3071 Fin15AnchoredAtom3085
    Fin15AnchoredAtom3185 Fin15AnchoredAtom3305 Fin15AnchoredAtom4130 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 12, 14}, {1, 4, 8, 12, 14}, {1, 3, 8, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 8, 14}, {1, 3, 4, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29612 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3070 chi ∧
      Fin15AnchoredAtom3071 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom4131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3070 Fin15AnchoredAtom3071 Fin15AnchoredAtom3086
    Fin15AnchoredAtom3186 Fin15AnchoredAtom3306 Fin15AnchoredAtom4131 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 8, 13, 14}, {1, 4, 8, 13, 14}, {1, 3, 8, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 8, 14}, {1, 3, 4, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29613 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom4133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3072 Fin15AnchoredAtom3074 Fin15AnchoredAtom3078
    Fin15AnchoredAtom3188 Fin15AnchoredAtom3308 Fin15AnchoredAtom4133 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 3, 9, 10, 12}, {1, 3, 4, 10, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29614 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom4134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3072 Fin15AnchoredAtom3075 Fin15AnchoredAtom3079
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3309 Fin15AnchoredAtom4134 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29615 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3072 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom4135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3072 Fin15AnchoredAtom3076 Fin15AnchoredAtom3080
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3310 Fin15AnchoredAtom4135 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 3, 9, 10, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29616 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3073 chi ∧
      Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3081 chi ∧
      Fin15AnchoredAtom3191 chi ∧
      Fin15AnchoredAtom3311 chi ∧
      Fin15AnchoredAtom4136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3073 Fin15AnchoredAtom3074 Fin15AnchoredAtom3081
    Fin15AnchoredAtom3191 Fin15AnchoredAtom3311 Fin15AnchoredAtom4136 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 9, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 9, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 11, 12}, {1, 4, 9, 11, 12}, {1, 3, 9, 11, 12}, {1, 3, 4, 11, 12}, {1, 3, 4, 9, 12}, {1, 3, 4, 9, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29617 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom4139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3074 Fin15AnchoredAtom3075 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3314 Fin15AnchoredAtom4139 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 9, 13}, {1, 3, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29618 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3074 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom4140 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3074 Fin15AnchoredAtom3076 Fin15AnchoredAtom3085
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3315 Fin15AnchoredAtom4140 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29619 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3075 chi ∧
      Fin15AnchoredAtom3076 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom4141 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3075 Fin15AnchoredAtom3076 Fin15AnchoredAtom3086
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3316 Fin15AnchoredAtom4141 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 9, 14}, {1, 3, 4, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29620 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom4145 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3078 Fin15AnchoredAtom3079 Fin15AnchoredAtom3084
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3320 Fin15AnchoredAtom4145 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 4, 12, 13}, {1, 3, 4, 10, 13}, {1, 3, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29621 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3078 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom4146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3078 Fin15AnchoredAtom3080 Fin15AnchoredAtom3085
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3321 Fin15AnchoredAtom4146 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29622 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3079 chi ∧
      Fin15AnchoredAtom3080 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom4147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3079 Fin15AnchoredAtom3080 Fin15AnchoredAtom3086
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3322 Fin15AnchoredAtom4147 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 10, 14}, {1, 3, 4, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29623 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3084 chi ∧
      Fin15AnchoredAtom3085 chi ∧
      Fin15AnchoredAtom3086 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom4151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3084 Fin15AnchoredAtom3085 Fin15AnchoredAtom3086
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3326 Fin15AnchoredAtom4151 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 4, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 4, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 4, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 4, 13, 14}, {1, 3, 4, 12, 14}, {1, 3, 4, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29624 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom3327 chi ∧
      Fin15AnchoredAtom4152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3088 Fin15AnchoredAtom3095
    Fin15AnchoredAtom3123 Fin15AnchoredAtom3327 Fin15AnchoredAtom4152 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 8}, {1, 5, 6, 7, 8}, {1, 3, 6, 7, 8}, {1, 3, 5, 7, 8}, {1, 3, 5, 6, 8}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29625 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom4153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3089 Fin15AnchoredAtom3096
    Fin15AnchoredAtom3124 Fin15AnchoredAtom3328 Fin15AnchoredAtom4153 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 9}, {1, 5, 6, 7, 9}, {1, 3, 6, 7, 9}, {1, 3, 5, 7, 9}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29626 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom4154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3090 Fin15AnchoredAtom3097
    Fin15AnchoredAtom3125 Fin15AnchoredAtom3329 Fin15AnchoredAtom4154 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 10}, {1, 5, 6, 7, 10}, {1, 3, 6, 7, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29627 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom4156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3092 Fin15AnchoredAtom3099
    Fin15AnchoredAtom3127 Fin15AnchoredAtom3331 Fin15AnchoredAtom4156 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 12}, {1, 5, 6, 7, 12}, {1, 3, 6, 7, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29628 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom4157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3093 Fin15AnchoredAtom3100
    Fin15AnchoredAtom3128 Fin15AnchoredAtom3332 Fin15AnchoredAtom4157 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 13}, {1, 5, 6, 7, 13}, {1, 3, 6, 7, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29629 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3087 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom4158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3087 Fin15AnchoredAtom3094 Fin15AnchoredAtom3101
    Fin15AnchoredAtom3129 Fin15AnchoredAtom3333 Fin15AnchoredAtom4158 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 7, 14}, {1, 5, 6, 7, 14}, {1, 3, 6, 7, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29630 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3334 chi ∧
      Fin15AnchoredAtom4159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3088 Fin15AnchoredAtom3089 Fin15AnchoredAtom3102
    Fin15AnchoredAtom3130 Fin15AnchoredAtom3334 Fin15AnchoredAtom4159 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 8, 9}, {1, 5, 6, 8, 9}, {1, 3, 6, 8, 9}, {1, 3, 5, 8, 9}, {1, 3, 5, 6, 9}, {1, 3, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29631 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3088 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3338 chi ∧
      Fin15AnchoredAtom4163 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3088 Fin15AnchoredAtom3093 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3134 Fin15AnchoredAtom3338 Fin15AnchoredAtom4163 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 8, 13}, {1, 5, 6, 8, 13}, {1, 3, 6, 8, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29632 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom4165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3089 Fin15AnchoredAtom3090 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3136 Fin15AnchoredAtom3340 Fin15AnchoredAtom4165 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 10}, {1, 5, 6, 9, 10}, {1, 3, 6, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 6, 10}, {1, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29633 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom4167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3089 Fin15AnchoredAtom3092 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3138 Fin15AnchoredAtom3342 Fin15AnchoredAtom4167 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 12}, {1, 5, 6, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29634 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom4168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3089 Fin15AnchoredAtom3093 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3139 Fin15AnchoredAtom3343 Fin15AnchoredAtom4168 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 13}, {1, 5, 6, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29635 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3089 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom4169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3089 Fin15AnchoredAtom3094 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3140 Fin15AnchoredAtom3344 Fin15AnchoredAtom4169 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 9, 14}, {1, 5, 6, 9, 14}, {1, 3, 6, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29636 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom4171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3090 Fin15AnchoredAtom3092 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3142 Fin15AnchoredAtom3346 Fin15AnchoredAtom4171 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 12}, {1, 5, 6, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29637 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom4172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3090 Fin15AnchoredAtom3093 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3143 Fin15AnchoredAtom3347 Fin15AnchoredAtom4172 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 13}, {1, 5, 6, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29638 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3090 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom4173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3090 Fin15AnchoredAtom3094 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3144 Fin15AnchoredAtom3348 Fin15AnchoredAtom4173 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 10, 14}, {1, 5, 6, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29639 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3091 chi ∧
      Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3117 chi ∧
      Fin15AnchoredAtom3145 chi ∧
      Fin15AnchoredAtom3349 chi ∧
      Fin15AnchoredAtom4174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3091 Fin15AnchoredAtom3092 Fin15AnchoredAtom3117
    Fin15AnchoredAtom3145 Fin15AnchoredAtom3349 Fin15AnchoredAtom4174 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 11, 12}, {1, 5, 6, 11, 12}, {1, 3, 6, 11, 12}, {1, 3, 5, 11, 12}, {1, 3, 5, 6, 12}, {1, 3, 5, 6, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29640 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom4177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3092 Fin15AnchoredAtom3093 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3148 Fin15AnchoredAtom3352 Fin15AnchoredAtom4177 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 12, 13}, {1, 5, 6, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 6, 13}, {1, 3, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29641 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3092 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom4178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3092 Fin15AnchoredAtom3094 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3149 Fin15AnchoredAtom3353 Fin15AnchoredAtom4178 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 12, 14}, {1, 5, 6, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29642 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3093 chi ∧
      Fin15AnchoredAtom3094 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom4179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3093 Fin15AnchoredAtom3094 Fin15AnchoredAtom3122
    Fin15AnchoredAtom3150 Fin15AnchoredAtom3354 Fin15AnchoredAtom4179 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 6, 13, 14}, {1, 5, 6, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 6, 14}, {1, 3, 5, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29643 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom3355 chi ∧
      Fin15AnchoredAtom4180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3095 Fin15AnchoredAtom3096 Fin15AnchoredAtom3102
    Fin15AnchoredAtom3151 Fin15AnchoredAtom3355 Fin15AnchoredAtom4180 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 8, 9}, {1, 5, 7, 8, 9}, {1, 3, 7, 8, 9}, {1, 3, 5, 8, 9}, {1, 3, 5, 7, 9}, {1, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29644 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom3356 chi ∧
      Fin15AnchoredAtom4181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3095 Fin15AnchoredAtom3097 Fin15AnchoredAtom3103
    Fin15AnchoredAtom3152 Fin15AnchoredAtom3356 Fin15AnchoredAtom4181 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 8, 10}, {1, 5, 7, 8, 10}, {1, 3, 7, 8, 10}, {1, 3, 5, 8, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29645 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom3358 chi ∧
      Fin15AnchoredAtom4183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3095 Fin15AnchoredAtom3099 Fin15AnchoredAtom3105
    Fin15AnchoredAtom3154 Fin15AnchoredAtom3358 Fin15AnchoredAtom4183 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 8, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 8, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 8, 12}, {1, 5, 7, 8, 12}, {1, 3, 7, 8, 12}, {1, 3, 5, 8, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29646 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3095 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3359 chi ∧
      Fin15AnchoredAtom4184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3095 Fin15AnchoredAtom3100 Fin15AnchoredAtom3106
    Fin15AnchoredAtom3155 Fin15AnchoredAtom3359 Fin15AnchoredAtom4184 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 8, 13}, {1, 5, 7, 8, 13}, {1, 3, 7, 8, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29647 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom4186 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3096 Fin15AnchoredAtom3097 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3361 Fin15AnchoredAtom4186 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 10}, {1, 5, 7, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 7, 10}, {1, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29648 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom4188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3096 Fin15AnchoredAtom3099 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3363 Fin15AnchoredAtom4188 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 12}, {1, 5, 7, 9, 12}, {1, 3, 7, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29649 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom4189 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3096 Fin15AnchoredAtom3100 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3364 Fin15AnchoredAtom4189 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 13}, {1, 5, 7, 9, 13}, {1, 3, 7, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29650 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3096 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom4190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3096 Fin15AnchoredAtom3101 Fin15AnchoredAtom3112
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3365 Fin15AnchoredAtom4190 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 9, 14}, {1, 5, 7, 9, 14}, {1, 3, 7, 9, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29651 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom4192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3097 Fin15AnchoredAtom3099 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3367 Fin15AnchoredAtom4192 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 12}, {1, 5, 7, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 7, 12}, {1, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29652 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom4193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3097 Fin15AnchoredAtom3100 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3368 Fin15AnchoredAtom4193 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 13}, {1, 5, 7, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29653 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3097 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom4194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3097 Fin15AnchoredAtom3101 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3369 Fin15AnchoredAtom4194 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 10, 14}, {1, 5, 7, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29654 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom4198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3099 Fin15AnchoredAtom3100 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3373 Fin15AnchoredAtom4198 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 12, 13}, {1, 5, 7, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 7, 13}, {1, 3, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29655 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3099 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom4199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3099 Fin15AnchoredAtom3101 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3374 Fin15AnchoredAtom4199 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 12, 14}, {1, 5, 7, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29656 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3100 chi ∧
      Fin15AnchoredAtom3101 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom4200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3100 Fin15AnchoredAtom3101 Fin15AnchoredAtom3122
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3375 Fin15AnchoredAtom4200 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 7, 13, 14}, {1, 5, 7, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 7, 14}, {1, 3, 5, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29657 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom3376 chi ∧
      Fin15AnchoredAtom4201 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3102 Fin15AnchoredAtom3103 Fin15AnchoredAtom3108
    Fin15AnchoredAtom3172 Fin15AnchoredAtom3376 Fin15AnchoredAtom4201 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 9, 10}, {1, 5, 8, 9, 10}, {1, 3, 8, 9, 10}, {1, 3, 5, 9, 10}, {1, 3, 5, 8, 10}, {1, 3, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29658 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom3378 chi ∧
      Fin15AnchoredAtom4203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3102 Fin15AnchoredAtom3105 Fin15AnchoredAtom3110
    Fin15AnchoredAtom3174 Fin15AnchoredAtom3378 Fin15AnchoredAtom4203 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 9, 12}, {1, 5, 8, 9, 12}, {1, 3, 8, 9, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 8, 12}, {1, 3, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29659 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3102 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3379 chi ∧
      Fin15AnchoredAtom4204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3102 Fin15AnchoredAtom3106 Fin15AnchoredAtom3111
    Fin15AnchoredAtom3175 Fin15AnchoredAtom3379 Fin15AnchoredAtom4204 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 9, 13}, {1, 5, 8, 9, 13}, {1, 3, 8, 9, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29660 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3103 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom4208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3103 Fin15AnchoredAtom3106 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3179 Fin15AnchoredAtom3383 Fin15AnchoredAtom4208 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 10, 13}, {1, 5, 8, 10, 13}, {1, 3, 8, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29661 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3105 chi ∧
      Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom4213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3105 Fin15AnchoredAtom3106 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3184 Fin15AnchoredAtom3388 Fin15AnchoredAtom4213 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 12, 13}, {1, 5, 8, 12, 13}, {1, 3, 8, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 8, 13}, {1, 3, 5, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29662 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3106 chi ∧
      Fin15AnchoredAtom3107 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3390 chi ∧
      Fin15AnchoredAtom4215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3106 Fin15AnchoredAtom3107 Fin15AnchoredAtom3122
    Fin15AnchoredAtom3186 Fin15AnchoredAtom3390 Fin15AnchoredAtom4215 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 8, 13, 14}, {1, 5, 8, 13, 14}, {1, 3, 8, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 8, 14}, {1, 3, 5, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29663 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom4217 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3108 Fin15AnchoredAtom3110 Fin15AnchoredAtom3114
    Fin15AnchoredAtom3188 Fin15AnchoredAtom3392 Fin15AnchoredAtom4217 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 3, 9, 10, 12}, {1, 3, 5, 10, 12}, {1, 3, 5, 9, 12}, {1, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29664 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom4218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3108 Fin15AnchoredAtom3111 Fin15AnchoredAtom3115
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3393 Fin15AnchoredAtom4218 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29665 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3108 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom4219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3108 Fin15AnchoredAtom3112 Fin15AnchoredAtom3116
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3394 Fin15AnchoredAtom4219 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 3, 9, 10, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29666 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom4223 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3110 Fin15AnchoredAtom3111 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3398 Fin15AnchoredAtom4223 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 9, 13}, {1, 3, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29667 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3110 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom4224 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3110 Fin15AnchoredAtom3112 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3399 Fin15AnchoredAtom4224 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29668 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3111 chi ∧
      Fin15AnchoredAtom3112 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom4225 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3111 Fin15AnchoredAtom3112 Fin15AnchoredAtom3122
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3400 Fin15AnchoredAtom4225 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 9, 14}, {1, 3, 5, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29669 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom4229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3114 Fin15AnchoredAtom3115 Fin15AnchoredAtom3120
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3404 Fin15AnchoredAtom4229 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 5, 12, 13}, {1, 3, 5, 10, 13}, {1, 3, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29670 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3114 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom4230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3114 Fin15AnchoredAtom3116 Fin15AnchoredAtom3121
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3405 Fin15AnchoredAtom4230 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29671 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3115 chi ∧
      Fin15AnchoredAtom3116 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom4231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3115 Fin15AnchoredAtom3116 Fin15AnchoredAtom3122
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3406 Fin15AnchoredAtom4231 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 10, 14}, {1, 3, 5, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29672 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3120 chi ∧
      Fin15AnchoredAtom3121 chi ∧
      Fin15AnchoredAtom3122 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom4235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3120 Fin15AnchoredAtom3121 Fin15AnchoredAtom3122
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3410 Fin15AnchoredAtom4235 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 5, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 5, 13, 14}, {1, 3, 5, 12, 14}, {1, 3, 5, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29673 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom3411 chi ∧
      Fin15AnchoredAtom4236 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3123 Fin15AnchoredAtom3124 Fin15AnchoredAtom3130
    Fin15AnchoredAtom3151 Fin15AnchoredAtom3411 Fin15AnchoredAtom4236 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 8, 9}, {1, 6, 7, 8, 9}, {1, 3, 7, 8, 9}, {1, 3, 6, 8, 9}, {1, 3, 6, 7, 9}, {1, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29674 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3123 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3415 chi ∧
      Fin15AnchoredAtom4240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3123 Fin15AnchoredAtom3128 Fin15AnchoredAtom3134
    Fin15AnchoredAtom3155 Fin15AnchoredAtom3415 Fin15AnchoredAtom4240 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 8, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 8, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 8, 13}, {1, 6, 7, 8, 13}, {1, 3, 7, 8, 13}, {1, 3, 6, 8, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29675 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom4242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3124 Fin15AnchoredAtom3125 Fin15AnchoredAtom3136
    Fin15AnchoredAtom3157 Fin15AnchoredAtom3417 Fin15AnchoredAtom4242 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 10}, {1, 6, 7, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 6, 9, 10}, {1, 3, 6, 7, 10}, {1, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29676 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom4244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3124 Fin15AnchoredAtom3127 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3159 Fin15AnchoredAtom3419 Fin15AnchoredAtom4244 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 12}, {1, 6, 7, 9, 12}, {1, 3, 7, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29677 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom4245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3124 Fin15AnchoredAtom3128 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3160 Fin15AnchoredAtom3420 Fin15AnchoredAtom4245 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 13}, {1, 6, 7, 9, 13}, {1, 3, 7, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29678 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3124 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom4246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3124 Fin15AnchoredAtom3129 Fin15AnchoredAtom3140
    Fin15AnchoredAtom3161 Fin15AnchoredAtom3421 Fin15AnchoredAtom4246 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 9, 14}, {1, 6, 7, 9, 14}, {1, 3, 7, 9, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29679 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom4248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3125 Fin15AnchoredAtom3127 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3163 Fin15AnchoredAtom3423 Fin15AnchoredAtom4248 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 12}, {1, 6, 7, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 7, 12}, {1, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29680 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom4249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3125 Fin15AnchoredAtom3128 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3164 Fin15AnchoredAtom3424 Fin15AnchoredAtom4249 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 13}, {1, 6, 7, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29681 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3125 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom4250 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3125 Fin15AnchoredAtom3129 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3165 Fin15AnchoredAtom3425 Fin15AnchoredAtom4250 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 10, 14}, {1, 6, 7, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29682 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom4254 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3127 Fin15AnchoredAtom3128 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3169 Fin15AnchoredAtom3429 Fin15AnchoredAtom4254 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 12, 13}, {1, 6, 7, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 7, 13}, {1, 3, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29683 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3127 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom4255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3127 Fin15AnchoredAtom3129 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3170 Fin15AnchoredAtom3430 Fin15AnchoredAtom4255 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 12, 14}, {1, 6, 7, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29684 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3128 chi ∧
      Fin15AnchoredAtom3129 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom4256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3128 Fin15AnchoredAtom3129 Fin15AnchoredAtom3150
    Fin15AnchoredAtom3171 Fin15AnchoredAtom3431 Fin15AnchoredAtom4256 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 7, 13, 14}, {1, 6, 7, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 7, 14}, {1, 3, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29685 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3133 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom3434 chi ∧
      Fin15AnchoredAtom4259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3130 Fin15AnchoredAtom3133 Fin15AnchoredAtom3138
    Fin15AnchoredAtom3174 Fin15AnchoredAtom3434 Fin15AnchoredAtom4259 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 8, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 8, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 9, 12}, {1, 6, 8, 9, 12}, {1, 3, 8, 9, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 8, 12}, {1, 3, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29686 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3130 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3435 chi ∧
      Fin15AnchoredAtom4260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3130 Fin15AnchoredAtom3134 Fin15AnchoredAtom3139
    Fin15AnchoredAtom3175 Fin15AnchoredAtom3435 Fin15AnchoredAtom4260 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 9, 13}, {1, 6, 8, 9, 13}, {1, 3, 8, 9, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 8, 13}, {1, 3, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29687 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3131 chi ∧
      Fin15AnchoredAtom3133 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom3438 chi ∧
      Fin15AnchoredAtom4263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3131 Fin15AnchoredAtom3133 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3178 Fin15AnchoredAtom3438 Fin15AnchoredAtom4263 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 10, 12}, {1, 6, 8, 10, 12}, {1, 3, 8, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 8, 12}, {1, 3, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29688 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3133 chi ∧
      Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom4269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3133 Fin15AnchoredAtom3134 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3184 Fin15AnchoredAtom3444 Fin15AnchoredAtom4269 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 12, 13}, {1, 6, 8, 12, 13}, {1, 3, 8, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 8, 13}, {1, 3, 6, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29689 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3134 chi ∧
      Fin15AnchoredAtom3135 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3446 chi ∧
      Fin15AnchoredAtom4271 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3134 Fin15AnchoredAtom3135 Fin15AnchoredAtom3150
    Fin15AnchoredAtom3186 Fin15AnchoredAtom3446 Fin15AnchoredAtom4271 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 8, 13, 14}, {1, 6, 8, 13, 14}, {1, 3, 8, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 8, 14}, {1, 3, 6, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29690 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom4273 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3136 Fin15AnchoredAtom3138 Fin15AnchoredAtom3142
    Fin15AnchoredAtom3188 Fin15AnchoredAtom3448 Fin15AnchoredAtom4273 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 3, 9, 10, 12}, {1, 3, 6, 10, 12}, {1, 3, 6, 9, 12}, {1, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29691 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom4274 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3136 Fin15AnchoredAtom3139 Fin15AnchoredAtom3143
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3449 Fin15AnchoredAtom4274 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29692 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom4275 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3136 Fin15AnchoredAtom3140 Fin15AnchoredAtom3144
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3450 Fin15AnchoredAtom4275 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 3, 9, 10, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29693 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom4279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3138 Fin15AnchoredAtom3139 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3454 Fin15AnchoredAtom4279 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 9, 13}, {1, 3, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29694 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom4280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3138 Fin15AnchoredAtom3140 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3455 Fin15AnchoredAtom4280 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29695 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom4281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3139 Fin15AnchoredAtom3140 Fin15AnchoredAtom3150
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3456 Fin15AnchoredAtom4281 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 9, 14}, {1, 3, 6, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
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
