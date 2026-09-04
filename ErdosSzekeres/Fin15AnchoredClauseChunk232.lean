module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 232. -/

theorem fin15Anchored_clause29696 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom4285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3142 Fin15AnchoredAtom3143 Fin15AnchoredAtom3148
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3460 Fin15AnchoredAtom4285 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 6, 12, 13}, {1, 3, 6, 10, 13}, {1, 3, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29697 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom4286 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3142 Fin15AnchoredAtom3144 Fin15AnchoredAtom3149
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3461 Fin15AnchoredAtom4286 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29698 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom4287 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3143 Fin15AnchoredAtom3144 Fin15AnchoredAtom3150
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3462 Fin15AnchoredAtom4287 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 10, 14}, {1, 3, 6, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29699 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom4291 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3148 Fin15AnchoredAtom3149 Fin15AnchoredAtom3150
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3466 Fin15AnchoredAtom4291 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 6, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 6, 13, 14}, {1, 3, 6, 12, 14}, {1, 3, 6, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29700 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom3467 chi ∧
      Fin15AnchoredAtom4292 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3151 Fin15AnchoredAtom3152 Fin15AnchoredAtom3157
    Fin15AnchoredAtom3172 Fin15AnchoredAtom3467 Fin15AnchoredAtom4292 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 9, 10}, {1, 7, 8, 9, 10}, {1, 3, 8, 9, 10}, {1, 3, 7, 9, 10}, {1, 3, 7, 8, 10}, {1, 3, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29701 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom3473 chi ∧
      Fin15AnchoredAtom4298 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3152 Fin15AnchoredAtom3154 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3178 Fin15AnchoredAtom3473 Fin15AnchoredAtom4298 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 10, 12}, {1, 7, 8, 10, 12}, {1, 3, 8, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 8, 12}, {1, 3, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29702 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3479 chi ∧
      Fin15AnchoredAtom4304 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3154 Fin15AnchoredAtom3155 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3184 Fin15AnchoredAtom3479 Fin15AnchoredAtom4304 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 12, 13}, {1, 7, 8, 12, 13}, {1, 3, 8, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 8, 13}, {1, 3, 7, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29703 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom3156 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3481 chi ∧
      Fin15AnchoredAtom4306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3155 Fin15AnchoredAtom3156 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3186 Fin15AnchoredAtom3481 Fin15AnchoredAtom4306 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 8, 13, 14}, {1, 7, 8, 13, 14}, {1, 3, 8, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 8, 14}, {1, 3, 7, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29704 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom4308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3157 Fin15AnchoredAtom3159 Fin15AnchoredAtom3163
    Fin15AnchoredAtom3188 Fin15AnchoredAtom3483 Fin15AnchoredAtom4308 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 12}, {1, 7, 9, 10, 12}, {1, 3, 9, 10, 12}, {1, 3, 7, 10, 12}, {1, 3, 7, 9, 12}, {1, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29705 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom4309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3157 Fin15AnchoredAtom3160 Fin15AnchoredAtom3164
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3484 Fin15AnchoredAtom4309 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 13}, {1, 7, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29706 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom4310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3157 Fin15AnchoredAtom3161 Fin15AnchoredAtom3165
    Fin15AnchoredAtom3190 Fin15AnchoredAtom3485 Fin15AnchoredAtom4310 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 10, 14}, {1, 7, 9, 10, 14}, {1, 3, 9, 10, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29707 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom4314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3159 Fin15AnchoredAtom3160 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3489 Fin15AnchoredAtom4314 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 12, 13}, {1, 7, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 9, 13}, {1, 3, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29708 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom4315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3159 Fin15AnchoredAtom3161 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3490 Fin15AnchoredAtom4315 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 12, 14}, {1, 7, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29709 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom4316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3160 Fin15AnchoredAtom3161 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3196 Fin15AnchoredAtom3491 Fin15AnchoredAtom4316 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 9, 13, 14}, {1, 7, 9, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 9, 14}, {1, 3, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29710 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom4320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3163 Fin15AnchoredAtom3164 Fin15AnchoredAtom3169
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3495 Fin15AnchoredAtom4320 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 7, 12, 13}, {1, 3, 7, 10, 13}, {1, 3, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29711 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom4321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3163 Fin15AnchoredAtom3165 Fin15AnchoredAtom3170
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3496 Fin15AnchoredAtom4321 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29712 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom4322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3164 Fin15AnchoredAtom3165 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3497 Fin15AnchoredAtom4322 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 10, 14}, {1, 3, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29713 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom4326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3169 Fin15AnchoredAtom3170 Fin15AnchoredAtom3171
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3501 Fin15AnchoredAtom4326 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 7, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 7, 13, 14}, {1, 3, 7, 12, 14}, {1, 3, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29714 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3504 chi ∧
      Fin15AnchoredAtom4329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3172 Fin15AnchoredAtom3175 Fin15AnchoredAtom3179
    Fin15AnchoredAtom3189 Fin15AnchoredAtom3504 Fin15AnchoredAtom4329 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 9, 10, 13}, {1, 8, 9, 10, 13}, {1, 3, 9, 10, 13}, {1, 3, 8, 10, 13}, {1, 3, 8, 9, 13}, {1, 3, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29715 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom4334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3174 Fin15AnchoredAtom3175 Fin15AnchoredAtom3184
    Fin15AnchoredAtom3194 Fin15AnchoredAtom3509 Fin15AnchoredAtom4334 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 9, 12, 13}, {1, 8, 9, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 8, 12, 13}, {1, 3, 8, 9, 13}, {1, 3, 8, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29716 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom3176 chi ∧
      Fin15AnchoredAtom3185 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3510 chi ∧
      Fin15AnchoredAtom4335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3174 Fin15AnchoredAtom3176 Fin15AnchoredAtom3185
    Fin15AnchoredAtom3195 Fin15AnchoredAtom3510 Fin15AnchoredAtom4335 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 8, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 9, 12, 14}, {1, 8, 9, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 8, 12, 14}, {1, 3, 8, 9, 14}, {1, 3, 8, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29717 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom4340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3178 Fin15AnchoredAtom3179 Fin15AnchoredAtom3184
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3515 Fin15AnchoredAtom4340 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 10, 12, 13}, {1, 8, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 8, 12, 13}, {1, 3, 8, 10, 13}, {1, 3, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29718 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom3180 chi ∧
      Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3517 chi ∧
      Fin15AnchoredAtom4342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3179 Fin15AnchoredAtom3180 Fin15AnchoredAtom3186
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3517 Fin15AnchoredAtom4342 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 8, 10, 13, 14}, {1, 8, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 8, 13, 14}, {1, 3, 8, 10, 14}, {1, 3, 8, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29719 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3188 Fin15AnchoredAtom3189 Fin15AnchoredAtom3194
    Fin15AnchoredAtom3200 Fin15AnchoredAtom3525 Fin15AnchoredAtom4350 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 12, 13}, {1, 9, 10, 12, 13}, {1, 3, 10, 12, 13}, {1, 3, 9, 12, 13}, {1, 3, 9, 10, 13}, {1, 3, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29720 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3188 Fin15AnchoredAtom3190 Fin15AnchoredAtom3195
    Fin15AnchoredAtom3201 Fin15AnchoredAtom3526 Fin15AnchoredAtom4351 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 12, 14}, {1, 9, 10, 12, 14}, {1, 3, 10, 12, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29721 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4352 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3189 Fin15AnchoredAtom3190 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3202 Fin15AnchoredAtom3527 Fin15AnchoredAtom4352 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 10, 13, 14}, {1, 9, 10, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 10, 14}, {1, 3, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29722 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom3195 chi ∧
      Fin15AnchoredAtom3196 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3194 Fin15AnchoredAtom3195 Fin15AnchoredAtom3196
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3531 Fin15AnchoredAtom4356 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 9, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 9, 13, 14}, {1, 3, 9, 12, 14}, {1, 3, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29723 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3200 chi ∧
      Fin15AnchoredAtom3201 chi ∧
      Fin15AnchoredAtom3202 chi ∧
      Fin15AnchoredAtom3206 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3200 Fin15AnchoredAtom3201 Fin15AnchoredAtom3202
    Fin15AnchoredAtom3206 Fin15AnchoredAtom3535 Fin15AnchoredAtom4360 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 3, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 3, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 3, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{3, 10, 12, 13, 14}, {1, 10, 12, 13, 14}, {1, 3, 12, 13, 14}, {1, 3, 10, 13, 14}, {1, 3, 10, 12, 14}, {1, 3, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29724 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom3215 chi ∧
      Fin15AnchoredAtom3243 chi ∧
      Fin15AnchoredAtom3327 chi ∧
      Fin15AnchoredAtom4362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3208 Fin15AnchoredAtom3215
    Fin15AnchoredAtom3243 Fin15AnchoredAtom3327 Fin15AnchoredAtom4362 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 7, 8}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 7, 8} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 8}, {1, 5, 6, 7, 8}, {1, 4, 6, 7, 8}, {1, 4, 5, 7, 8}, {1, 4, 5, 6, 8}, {1, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29725 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom4363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3209 Fin15AnchoredAtom3216
    Fin15AnchoredAtom3244 Fin15AnchoredAtom3328 Fin15AnchoredAtom4363 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 7, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 7, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 9}, {1, 5, 6, 7, 9}, {1, 4, 6, 7, 9}, {1, 4, 5, 7, 9}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29726 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom4364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3210 Fin15AnchoredAtom3217
    Fin15AnchoredAtom3245 Fin15AnchoredAtom3329 Fin15AnchoredAtom4364 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 7, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 7, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 10}, {1, 5, 6, 7, 10}, {1, 4, 6, 7, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29727 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom4366 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3212 Fin15AnchoredAtom3219
    Fin15AnchoredAtom3247 Fin15AnchoredAtom3331 Fin15AnchoredAtom4366 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 7, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 7, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 12}, {1, 5, 6, 7, 12}, {1, 4, 6, 7, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29728 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom4367 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3213 Fin15AnchoredAtom3220
    Fin15AnchoredAtom3248 Fin15AnchoredAtom3332 Fin15AnchoredAtom4367 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 7, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 7, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 13}, {1, 5, 6, 7, 13}, {1, 4, 6, 7, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29729 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3207 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom4368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3207 Fin15AnchoredAtom3214 Fin15AnchoredAtom3221
    Fin15AnchoredAtom3249 Fin15AnchoredAtom3333 Fin15AnchoredAtom4368 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 7, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 7, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 7, 14}, {1, 5, 6, 7, 14}, {1, 4, 6, 7, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 7}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29730 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3222 chi ∧
      Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom3334 chi ∧
      Fin15AnchoredAtom4369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3208 Fin15AnchoredAtom3209 Fin15AnchoredAtom3222
    Fin15AnchoredAtom3250 Fin15AnchoredAtom3334 Fin15AnchoredAtom4369 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 9}, {1, 5, 6, 8, 9}, {1, 4, 6, 8, 9}, {1, 4, 5, 8, 9}, {1, 4, 5, 6, 9}, {1, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29731 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3208 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom3335 chi ∧
      Fin15AnchoredAtom4370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3208 Fin15AnchoredAtom3210 Fin15AnchoredAtom3223
    Fin15AnchoredAtom3251 Fin15AnchoredAtom3335 Fin15AnchoredAtom4370 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 8, 10}, {1, 5, 6, 8, 10}, {1, 4, 6, 8, 10}, {1, 4, 5, 8, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29732 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom4375 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3209 Fin15AnchoredAtom3210 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3256 Fin15AnchoredAtom3340 Fin15AnchoredAtom4375 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 10}, {1, 5, 6, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 6, 10}, {1, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29733 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom4377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3209 Fin15AnchoredAtom3212 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3258 Fin15AnchoredAtom3342 Fin15AnchoredAtom4377 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 12}, {1, 5, 6, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29734 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom4378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3209 Fin15AnchoredAtom3213 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3259 Fin15AnchoredAtom3343 Fin15AnchoredAtom4378 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 13}, {1, 5, 6, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29735 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3209 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom4379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3209 Fin15AnchoredAtom3214 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3260 Fin15AnchoredAtom3344 Fin15AnchoredAtom4379 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 9, 14}, {1, 5, 6, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29736 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom4381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3210 Fin15AnchoredAtom3212 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3262 Fin15AnchoredAtom3346 Fin15AnchoredAtom4381 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 12}, {1, 5, 6, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 6, 12}, {1, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29737 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom4382 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3210 Fin15AnchoredAtom3213 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3263 Fin15AnchoredAtom3347 Fin15AnchoredAtom4382 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 13}, {1, 5, 6, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29738 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3210 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom4383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3210 Fin15AnchoredAtom3214 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3264 Fin15AnchoredAtom3348 Fin15AnchoredAtom4383 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 10, 14}, {1, 5, 6, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29739 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom4387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3212 Fin15AnchoredAtom3213 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3268 Fin15AnchoredAtom3352 Fin15AnchoredAtom4387 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 13}, {1, 5, 6, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 6, 13}, {1, 4, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29740 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3212 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom4388 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3212 Fin15AnchoredAtom3214 Fin15AnchoredAtom3241
    Fin15AnchoredAtom3269 Fin15AnchoredAtom3353 Fin15AnchoredAtom4388 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 12, 14}, {1, 5, 6, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29741 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3213 chi ∧
      Fin15AnchoredAtom3214 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3354 chi ∧
      Fin15AnchoredAtom4389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3213 Fin15AnchoredAtom3214 Fin15AnchoredAtom3242
    Fin15AnchoredAtom3270 Fin15AnchoredAtom3354 Fin15AnchoredAtom4389 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 6, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 6, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 6, 13, 14}, {1, 5, 6, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 6, 14}, {1, 4, 5, 6, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29742 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom4396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3216 Fin15AnchoredAtom3217 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3277 Fin15AnchoredAtom3361 Fin15AnchoredAtom4396 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 10}, {1, 5, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 7, 10}, {1, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29743 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom4398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3216 Fin15AnchoredAtom3219 Fin15AnchoredAtom3230
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3363 Fin15AnchoredAtom4398 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 12}, {1, 5, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29744 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom4399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3216 Fin15AnchoredAtom3220 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3364 Fin15AnchoredAtom4399 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 13}, {1, 5, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29745 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3216 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom4400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3216 Fin15AnchoredAtom3221 Fin15AnchoredAtom3232
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3365 Fin15AnchoredAtom4400 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 9, 14}, {1, 5, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29746 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom4402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3217 Fin15AnchoredAtom3219 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3367 Fin15AnchoredAtom4402 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 12}, {1, 5, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 7, 12}, {1, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29747 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom4403 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3217 Fin15AnchoredAtom3220 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3368 Fin15AnchoredAtom4403 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 13}, {1, 5, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29748 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3217 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom4404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3217 Fin15AnchoredAtom3221 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3369 Fin15AnchoredAtom4404 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 10, 14}, {1, 5, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29749 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom4408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3219 Fin15AnchoredAtom3220 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3373 Fin15AnchoredAtom4408 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 13}, {1, 5, 7, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 7, 13}, {1, 4, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29750 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3219 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom4409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3219 Fin15AnchoredAtom3221 Fin15AnchoredAtom3241
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3374 Fin15AnchoredAtom4409 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 12, 14}, {1, 5, 7, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29751 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3220 chi ∧
      Fin15AnchoredAtom3221 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom4410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3220 Fin15AnchoredAtom3221 Fin15AnchoredAtom3242
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3375 Fin15AnchoredAtom4410 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 7, 13, 14}, {1, 5, 7, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 7, 14}, {1, 4, 5, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29752 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3222 chi ∧
      Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom3376 chi ∧
      Fin15AnchoredAtom4411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3222 Fin15AnchoredAtom3223 Fin15AnchoredAtom3228
    Fin15AnchoredAtom3292 Fin15AnchoredAtom3376 Fin15AnchoredAtom4411 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 10}, {1, 5, 8, 9, 10}, {1, 4, 8, 9, 10}, {1, 4, 5, 9, 10}, {1, 4, 5, 8, 10}, {1, 4, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29753 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3222 chi ∧
      Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom3379 chi ∧
      Fin15AnchoredAtom4414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3222 Fin15AnchoredAtom3226 Fin15AnchoredAtom3231
    Fin15AnchoredAtom3295 Fin15AnchoredAtom3379 Fin15AnchoredAtom4414 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 9, 13}, {1, 5, 8, 9, 13}, {1, 4, 8, 9, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29754 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3223 chi ∧
      Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom4418 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3223 Fin15AnchoredAtom3226 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3299 Fin15AnchoredAtom3383 Fin15AnchoredAtom4418 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 10, 13}, {1, 5, 8, 10, 13}, {1, 4, 8, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29755 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3225 chi ∧
      Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom4423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3225 Fin15AnchoredAtom3226 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3304 Fin15AnchoredAtom3388 Fin15AnchoredAtom4423 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 12, 13}, {1, 5, 8, 12, 13}, {1, 4, 8, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 8, 13}, {1, 4, 5, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29756 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3226 chi ∧
      Fin15AnchoredAtom3227 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom3390 chi ∧
      Fin15AnchoredAtom4425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3226 Fin15AnchoredAtom3227 Fin15AnchoredAtom3242
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3390 Fin15AnchoredAtom4425 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 8, 13, 14}, {1, 5, 8, 13, 14}, {1, 4, 8, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 8, 14}, {1, 4, 5, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29757 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom4427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3228 Fin15AnchoredAtom3230 Fin15AnchoredAtom3234
    Fin15AnchoredAtom3308 Fin15AnchoredAtom3392 Fin15AnchoredAtom4427 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 12}, {1, 5, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 5, 10, 12}, {1, 4, 5, 9, 12}, {1, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29758 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom4428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3228 Fin15AnchoredAtom3231 Fin15AnchoredAtom3235
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3393 Fin15AnchoredAtom4428 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 13}, {1, 5, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29759 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3228 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom4429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3228 Fin15AnchoredAtom3232 Fin15AnchoredAtom3236
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3394 Fin15AnchoredAtom4429 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 10, 14}, {1, 5, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29760 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom4433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3230 Fin15AnchoredAtom3231 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3398 Fin15AnchoredAtom4433 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 13}, {1, 5, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 9, 13}, {1, 4, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29761 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3230 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom4434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3230 Fin15AnchoredAtom3232 Fin15AnchoredAtom3241
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3399 Fin15AnchoredAtom4434 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 12, 14}, {1, 5, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29762 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3231 chi ∧
      Fin15AnchoredAtom3232 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom4435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3231 Fin15AnchoredAtom3232 Fin15AnchoredAtom3242
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3400 Fin15AnchoredAtom4435 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 9, 13, 14}, {1, 5, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 9, 14}, {1, 4, 5, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29763 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom4439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3234 Fin15AnchoredAtom3235 Fin15AnchoredAtom3240
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3404 Fin15AnchoredAtom4439 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 13}, {1, 5, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 5, 12, 13}, {1, 4, 5, 10, 13}, {1, 4, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29764 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3234 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom4440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3234 Fin15AnchoredAtom3236 Fin15AnchoredAtom3241
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3405 Fin15AnchoredAtom4440 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 12, 14}, {1, 5, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29765 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3235 chi ∧
      Fin15AnchoredAtom3236 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom4441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3235 Fin15AnchoredAtom3236 Fin15AnchoredAtom3242
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3406 Fin15AnchoredAtom4441 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 10, 13, 14}, {1, 5, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 10, 14}, {1, 4, 5, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29766 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3240 chi ∧
      Fin15AnchoredAtom3241 chi ∧
      Fin15AnchoredAtom3242 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom4445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3240 Fin15AnchoredAtom3241 Fin15AnchoredAtom3242
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3410 Fin15AnchoredAtom4445 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 5, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 5, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 5, 12, 13, 14}, {1, 5, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 5, 13, 14}, {1, 4, 5, 12, 14}, {1, 4, 5, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29767 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3243 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3255 chi ∧
      Fin15AnchoredAtom3276 chi ∧
      Fin15AnchoredAtom3416 chi ∧
      Fin15AnchoredAtom4451 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3243 Fin15AnchoredAtom3249 Fin15AnchoredAtom3255
    Fin15AnchoredAtom3276 Fin15AnchoredAtom3416 Fin15AnchoredAtom4451 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 8, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 8, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 8, 14}, {1, 6, 7, 8, 14}, {1, 4, 7, 8, 14}, {1, 4, 6, 8, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29768 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom4452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3244 Fin15AnchoredAtom3245 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3277 Fin15AnchoredAtom3417 Fin15AnchoredAtom4452 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 10}, {1, 6, 7, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 6, 7, 10}, {1, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29769 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom4454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3244 Fin15AnchoredAtom3247 Fin15AnchoredAtom3258
    Fin15AnchoredAtom3279 Fin15AnchoredAtom3419 Fin15AnchoredAtom4454 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 12}, {1, 6, 7, 9, 12}, {1, 4, 7, 9, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29770 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom4455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3244 Fin15AnchoredAtom3248 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3280 Fin15AnchoredAtom3420 Fin15AnchoredAtom4455 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 13}, {1, 6, 7, 9, 13}, {1, 4, 7, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29771 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3244 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom4456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3244 Fin15AnchoredAtom3249 Fin15AnchoredAtom3260
    Fin15AnchoredAtom3281 Fin15AnchoredAtom3421 Fin15AnchoredAtom4456 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 9, 14}, {1, 6, 7, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29772 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom4458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3245 Fin15AnchoredAtom3247 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3283 Fin15AnchoredAtom3423 Fin15AnchoredAtom4458 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 12}, {1, 6, 7, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 7, 12}, {1, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29773 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom4459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3245 Fin15AnchoredAtom3248 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3284 Fin15AnchoredAtom3424 Fin15AnchoredAtom4459 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 13}, {1, 6, 7, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29774 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3245 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom4460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3245 Fin15AnchoredAtom3249 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3285 Fin15AnchoredAtom3425 Fin15AnchoredAtom4460 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 14}, {1, 6, 7, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29775 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom4464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3247 Fin15AnchoredAtom3248 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3289 Fin15AnchoredAtom3429 Fin15AnchoredAtom4464 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 13}, {1, 6, 7, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 7, 13}, {1, 4, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29776 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3247 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom4465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3247 Fin15AnchoredAtom3249 Fin15AnchoredAtom3269
    Fin15AnchoredAtom3290 Fin15AnchoredAtom3430 Fin15AnchoredAtom4465 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 14}, {1, 6, 7, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29777 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3248 chi ∧
      Fin15AnchoredAtom3249 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom4466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3248 Fin15AnchoredAtom3249 Fin15AnchoredAtom3270
    Fin15AnchoredAtom3291 Fin15AnchoredAtom3431 Fin15AnchoredAtom4466 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 13, 14}, {1, 6, 7, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 7, 14}, {1, 4, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29778 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom3432 chi ∧
      Fin15AnchoredAtom4467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3250 Fin15AnchoredAtom3251 Fin15AnchoredAtom3256
    Fin15AnchoredAtom3292 Fin15AnchoredAtom3432 Fin15AnchoredAtom4467 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 9, 10}, {1, 6, 8, 9, 10}, {1, 4, 8, 9, 10}, {1, 4, 6, 9, 10}, {1, 4, 6, 8, 10}, {1, 4, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29779 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3250 chi ∧
      Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom3435 chi ∧
      Fin15AnchoredAtom4470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3250 Fin15AnchoredAtom3254 Fin15AnchoredAtom3259
    Fin15AnchoredAtom3295 Fin15AnchoredAtom3435 Fin15AnchoredAtom4470 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 8, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 8, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 9, 13}, {1, 6, 8, 9, 13}, {1, 4, 8, 9, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 8, 13}, {1, 4, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29780 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3251 chi ∧
      Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom3439 chi ∧
      Fin15AnchoredAtom4474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3251 Fin15AnchoredAtom3254 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3299 Fin15AnchoredAtom3439 Fin15AnchoredAtom4474 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 10, 13}, {1, 6, 8, 10, 13}, {1, 4, 8, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 8, 13}, {1, 4, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29781 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3253 chi ∧
      Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom4479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3253 Fin15AnchoredAtom3254 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3304 Fin15AnchoredAtom3444 Fin15AnchoredAtom4479 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 12, 13}, {1, 6, 8, 12, 13}, {1, 4, 8, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 8, 13}, {1, 4, 6, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29782 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3254 chi ∧
      Fin15AnchoredAtom3255 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom3446 chi ∧
      Fin15AnchoredAtom4481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3254 Fin15AnchoredAtom3255 Fin15AnchoredAtom3270
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3446 Fin15AnchoredAtom4481 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 13, 14}, {1, 6, 8, 13, 14}, {1, 4, 8, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 8, 14}, {1, 4, 6, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29783 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom4483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3256 Fin15AnchoredAtom3258 Fin15AnchoredAtom3262
    Fin15AnchoredAtom3308 Fin15AnchoredAtom3448 Fin15AnchoredAtom4483 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 12}, {1, 6, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 6, 10, 12}, {1, 4, 6, 9, 12}, {1, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29784 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom4484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3256 Fin15AnchoredAtom3259 Fin15AnchoredAtom3263
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3449 Fin15AnchoredAtom4484 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 13}, {1, 6, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29785 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3256 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom4485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3256 Fin15AnchoredAtom3260 Fin15AnchoredAtom3264
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3450 Fin15AnchoredAtom4485 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 14}, {1, 6, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29786 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom4489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3258 Fin15AnchoredAtom3259 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3454 Fin15AnchoredAtom4489 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 13}, {1, 6, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 9, 13}, {1, 4, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29787 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3258 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom4490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3258 Fin15AnchoredAtom3260 Fin15AnchoredAtom3269
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3455 Fin15AnchoredAtom4490 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 14}, {1, 6, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29788 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3259 chi ∧
      Fin15AnchoredAtom3260 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom4491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3259 Fin15AnchoredAtom3260 Fin15AnchoredAtom3270
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3456 Fin15AnchoredAtom4491 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 13, 14}, {1, 6, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 9, 14}, {1, 4, 6, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29789 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3460 chi ∧
      Fin15AnchoredAtom4495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3262 Fin15AnchoredAtom3263 Fin15AnchoredAtom3268
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3460 Fin15AnchoredAtom4495 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 13}, {1, 6, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 6, 12, 13}, {1, 4, 6, 10, 13}, {1, 4, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29790 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3262 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3461 chi ∧
      Fin15AnchoredAtom4496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3262 Fin15AnchoredAtom3264 Fin15AnchoredAtom3269
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3461 Fin15AnchoredAtom4496 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 14}, {1, 6, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29791 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3263 chi ∧
      Fin15AnchoredAtom3264 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3462 chi ∧
      Fin15AnchoredAtom4497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3263 Fin15AnchoredAtom3264 Fin15AnchoredAtom3270
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3462 Fin15AnchoredAtom4497 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 13, 14}, {1, 6, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 10, 14}, {1, 4, 6, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29792 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3268 chi ∧
      Fin15AnchoredAtom3269 chi ∧
      Fin15AnchoredAtom3270 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3466 chi ∧
      Fin15AnchoredAtom4501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3268 Fin15AnchoredAtom3269 Fin15AnchoredAtom3270
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3466 Fin15AnchoredAtom4501 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 12, 13, 14}, {1, 6, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 6, 13, 14}, {1, 4, 6, 12, 14}, {1, 4, 6, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29793 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3271 chi ∧
      Fin15AnchoredAtom3272 chi ∧
      Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3292 chi ∧
      Fin15AnchoredAtom3467 chi ∧
      Fin15AnchoredAtom4502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3271 Fin15AnchoredAtom3272 Fin15AnchoredAtom3277
    Fin15AnchoredAtom3292 Fin15AnchoredAtom3467 Fin15AnchoredAtom4502 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 9, 10}, {1, 7, 8, 9, 10}, {1, 4, 8, 9, 10}, {1, 4, 7, 9, 10}, {1, 4, 7, 8, 10}, {1, 4, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29794 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3271 chi ∧
      Fin15AnchoredAtom3276 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3296 chi ∧
      Fin15AnchoredAtom3471 chi ∧
      Fin15AnchoredAtom4506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3271 Fin15AnchoredAtom3276 Fin15AnchoredAtom3281
    Fin15AnchoredAtom3296 Fin15AnchoredAtom3471 Fin15AnchoredAtom4506 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 9, 14}, {1, 7, 8, 9, 14}, {1, 4, 8, 9, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 8, 14}, {1, 4, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29795 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3274 chi ∧
      Fin15AnchoredAtom3275 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3479 chi ∧
      Fin15AnchoredAtom4514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3274 Fin15AnchoredAtom3275 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3304 Fin15AnchoredAtom3479 Fin15AnchoredAtom4514 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 12, 13}, {1, 7, 8, 12, 13}, {1, 4, 8, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 8, 13}, {1, 4, 7, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29796 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3275 chi ∧
      Fin15AnchoredAtom3276 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3306 chi ∧
      Fin15AnchoredAtom3481 chi ∧
      Fin15AnchoredAtom4516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3275 Fin15AnchoredAtom3276 Fin15AnchoredAtom3291
    Fin15AnchoredAtom3306 Fin15AnchoredAtom3481 Fin15AnchoredAtom4516 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 13, 14}, {1, 7, 8, 13, 14}, {1, 4, 8, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 8, 14}, {1, 4, 7, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29797 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3483 chi ∧
      Fin15AnchoredAtom4518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3277 Fin15AnchoredAtom3279 Fin15AnchoredAtom3283
    Fin15AnchoredAtom3308 Fin15AnchoredAtom3483 Fin15AnchoredAtom4518 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 12}, {1, 7, 9, 10, 12}, {1, 4, 9, 10, 12}, {1, 4, 7, 10, 12}, {1, 4, 7, 9, 12}, {1, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29798 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3484 chi ∧
      Fin15AnchoredAtom4519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3277 Fin15AnchoredAtom3280 Fin15AnchoredAtom3284
    Fin15AnchoredAtom3309 Fin15AnchoredAtom3484 Fin15AnchoredAtom4519 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 13}, {1, 7, 9, 10, 13}, {1, 4, 9, 10, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29799 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3277 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3485 chi ∧
      Fin15AnchoredAtom4520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3277 Fin15AnchoredAtom3281 Fin15AnchoredAtom3285
    Fin15AnchoredAtom3310 Fin15AnchoredAtom3485 Fin15AnchoredAtom4520 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 14}, {1, 7, 9, 10, 14}, {1, 4, 9, 10, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29800 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3489 chi ∧
      Fin15AnchoredAtom4524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3279 Fin15AnchoredAtom3280 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3489 Fin15AnchoredAtom4524 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 13}, {1, 7, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 9, 13}, {1, 4, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29801 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3279 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3490 chi ∧
      Fin15AnchoredAtom4525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3279 Fin15AnchoredAtom3281 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3490 Fin15AnchoredAtom4525 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 14}, {1, 7, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29802 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3280 chi ∧
      Fin15AnchoredAtom3281 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3491 chi ∧
      Fin15AnchoredAtom4526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3280 Fin15AnchoredAtom3281 Fin15AnchoredAtom3291
    Fin15AnchoredAtom3316 Fin15AnchoredAtom3491 Fin15AnchoredAtom4526 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 13, 14}, {1, 7, 9, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 9, 14}, {1, 4, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29803 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom4530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3283 Fin15AnchoredAtom3284 Fin15AnchoredAtom3289
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3495 Fin15AnchoredAtom4530 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 13}, {1, 7, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 7, 12, 13}, {1, 4, 7, 10, 13}, {1, 4, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29804 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3283 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom4531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3283 Fin15AnchoredAtom3285 Fin15AnchoredAtom3290
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3496 Fin15AnchoredAtom4531 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 14}, {1, 7, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29805 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3284 chi ∧
      Fin15AnchoredAtom3285 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom4532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3284 Fin15AnchoredAtom3285 Fin15AnchoredAtom3291
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3497 Fin15AnchoredAtom4532 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 13, 14}, {1, 7, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 10, 14}, {1, 4, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29806 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3289 chi ∧
      Fin15AnchoredAtom3290 chi ∧
      Fin15AnchoredAtom3291 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom4536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3289 Fin15AnchoredAtom3290 Fin15AnchoredAtom3291
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3501 Fin15AnchoredAtom4536 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 12, 13, 14}, {1, 7, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 7, 13, 14}, {1, 4, 7, 12, 14}, {1, 4, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29807 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3294 chi ∧
      Fin15AnchoredAtom3295 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom4544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3294 Fin15AnchoredAtom3295 Fin15AnchoredAtom3304
    Fin15AnchoredAtom3314 Fin15AnchoredAtom3509 Fin15AnchoredAtom4544 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 8, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 8, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 12, 13}, {1, 8, 9, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 8, 12, 13}, {1, 4, 8, 9, 13}, {1, 4, 8, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29808 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3294 chi ∧
      Fin15AnchoredAtom3296 chi ∧
      Fin15AnchoredAtom3305 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3510 chi ∧
      Fin15AnchoredAtom4545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3294 Fin15AnchoredAtom3296 Fin15AnchoredAtom3305
    Fin15AnchoredAtom3315 Fin15AnchoredAtom3510 Fin15AnchoredAtom4545 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 8, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 8, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 12, 14}, {1, 8, 9, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 8, 12, 14}, {1, 4, 8, 9, 14}, {1, 4, 8, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29809 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3298 chi ∧
      Fin15AnchoredAtom3299 chi ∧
      Fin15AnchoredAtom3304 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom4550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3298 Fin15AnchoredAtom3299 Fin15AnchoredAtom3304
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3515 Fin15AnchoredAtom4550 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 10, 12, 13}, {1, 8, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 8, 12, 13}, {1, 4, 8, 10, 13}, {1, 4, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29810 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom4560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3308 Fin15AnchoredAtom3309 Fin15AnchoredAtom3314
    Fin15AnchoredAtom3320 Fin15AnchoredAtom3525 Fin15AnchoredAtom4560 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 13}, {1, 9, 10, 12, 13}, {1, 4, 10, 12, 13}, {1, 4, 9, 12, 13}, {1, 4, 9, 10, 13}, {1, 4, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29811 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3308 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom4561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3308 Fin15AnchoredAtom3310 Fin15AnchoredAtom3315
    Fin15AnchoredAtom3321 Fin15AnchoredAtom3526 Fin15AnchoredAtom4561 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 14}, {1, 9, 10, 12, 14}, {1, 4, 10, 12, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29812 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3309 chi ∧
      Fin15AnchoredAtom3310 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom4562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3309 Fin15AnchoredAtom3310 Fin15AnchoredAtom3316
    Fin15AnchoredAtom3322 Fin15AnchoredAtom3527 Fin15AnchoredAtom4562 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 13, 14}, {1, 9, 10, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 10, 14}, {1, 4, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29813 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3314 chi ∧
      Fin15AnchoredAtom3315 chi ∧
      Fin15AnchoredAtom3316 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom4566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3314 Fin15AnchoredAtom3315 Fin15AnchoredAtom3316
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3531 Fin15AnchoredAtom4566 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 12, 13, 14}, {1, 9, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 9, 13, 14}, {1, 4, 9, 12, 14}, {1, 4, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29814 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3320 chi ∧
      Fin15AnchoredAtom3321 chi ∧
      Fin15AnchoredAtom3322 chi ∧
      Fin15AnchoredAtom3326 chi ∧
      Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom4570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3320 Fin15AnchoredAtom3321 Fin15AnchoredAtom3322
    Fin15AnchoredAtom3326 Fin15AnchoredAtom3535 Fin15AnchoredAtom4570 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 4, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 10, 12, 13, 14}, {1, 10, 12, 13, 14}, {1, 4, 12, 13, 14}, {1, 4, 10, 13, 14}, {1, 4, 10, 12, 14}, {1, 4, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29815 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3340 chi ∧
      Fin15AnchoredAtom3361 chi ∧
      Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom4578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3328 Fin15AnchoredAtom3329 Fin15AnchoredAtom3340
    Fin15AnchoredAtom3361 Fin15AnchoredAtom3417 Fin15AnchoredAtom4578 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {1, 6, 7, 9, 10}, {1, 5, 7, 9, 10}, {1, 5, 6, 9, 10}, {1, 5, 6, 7, 10}, {1, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29816 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3342 chi ∧
      Fin15AnchoredAtom3363 chi ∧
      Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom4580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3328 Fin15AnchoredAtom3331 Fin15AnchoredAtom3342
    Fin15AnchoredAtom3363 Fin15AnchoredAtom3419 Fin15AnchoredAtom4580 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {1, 6, 7, 9, 12}, {1, 5, 7, 9, 12}, {1, 5, 6, 9, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29817 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3343 chi ∧
      Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom4581 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3328 Fin15AnchoredAtom3332 Fin15AnchoredAtom3343
    Fin15AnchoredAtom3364 Fin15AnchoredAtom3420 Fin15AnchoredAtom4581 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {1, 6, 7, 9, 13}, {1, 5, 7, 9, 13}, {1, 5, 6, 9, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29818 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3328 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3344 chi ∧
      Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom4582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3328 Fin15AnchoredAtom3333 Fin15AnchoredAtom3344
    Fin15AnchoredAtom3365 Fin15AnchoredAtom3421 Fin15AnchoredAtom4582 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {1, 6, 7, 9, 14}, {1, 5, 7, 9, 14}, {1, 5, 6, 9, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29819 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3346 chi ∧
      Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom4584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3329 Fin15AnchoredAtom3331 Fin15AnchoredAtom3346
    Fin15AnchoredAtom3367 Fin15AnchoredAtom3423 Fin15AnchoredAtom4584 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {1, 6, 7, 10, 12}, {1, 5, 7, 10, 12}, {1, 5, 6, 10, 12}, {1, 5, 6, 7, 12}, {1, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29820 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3347 chi ∧
      Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom4585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3329 Fin15AnchoredAtom3332 Fin15AnchoredAtom3347
    Fin15AnchoredAtom3368 Fin15AnchoredAtom3424 Fin15AnchoredAtom4585 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {1, 6, 7, 10, 13}, {1, 5, 7, 10, 13}, {1, 5, 6, 10, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29821 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3329 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3348 chi ∧
      Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom4586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3329 Fin15AnchoredAtom3333 Fin15AnchoredAtom3348
    Fin15AnchoredAtom3369 Fin15AnchoredAtom3425 Fin15AnchoredAtom4586 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {1, 6, 7, 10, 14}, {1, 5, 7, 10, 14}, {1, 5, 6, 10, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29822 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3332 chi ∧
      Fin15AnchoredAtom3352 chi ∧
      Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom4590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3331 Fin15AnchoredAtom3332 Fin15AnchoredAtom3352
    Fin15AnchoredAtom3373 Fin15AnchoredAtom3429 Fin15AnchoredAtom4590 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {1, 6, 7, 12, 13}, {1, 5, 7, 12, 13}, {1, 5, 6, 12, 13}, {1, 5, 6, 7, 13}, {1, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause29823 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom3331 chi ∧
      Fin15AnchoredAtom3333 chi ∧
      Fin15AnchoredAtom3353 chi ∧
      Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom4591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom3331 Fin15AnchoredAtom3333 Fin15AnchoredAtom3353
    Fin15AnchoredAtom3374 Fin15AnchoredAtom3430 Fin15AnchoredAtom4591 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{1, 5, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({1, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({1, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {1, 6, 7, 12, 14}, {1, 5, 7, 12, 14}, {1, 5, 6, 12, 14}, {1, 5, 6, 7, 14}, {1, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
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
