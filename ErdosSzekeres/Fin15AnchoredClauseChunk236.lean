module

public import ErdosSzekeres.Fin15AnchoredSupport
public import ErdosSzekeres.StrongPolygonSubsets

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 236. -/

theorem fin15Anchored_clause30208 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4070 Fin15AnchoredAtom4072 Fin15AnchoredAtom4087
    Fin15AnchoredAtom4108 Fin15AnchoredAtom4248 Fin15AnchoredAtom4458 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 12}, {3, 6, 7, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 7, 12}, {3, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30209 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4070 Fin15AnchoredAtom4073 Fin15AnchoredAtom4088
    Fin15AnchoredAtom4109 Fin15AnchoredAtom4249 Fin15AnchoredAtom4459 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 13}, {3, 6, 7, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30210 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4070 Fin15AnchoredAtom4074 Fin15AnchoredAtom4089
    Fin15AnchoredAtom4110 Fin15AnchoredAtom4250 Fin15AnchoredAtom4460 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 10, 14}, {3, 6, 7, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30211 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4072 Fin15AnchoredAtom4073 Fin15AnchoredAtom4093
    Fin15AnchoredAtom4114 Fin15AnchoredAtom4254 Fin15AnchoredAtom4464 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 13}, {3, 6, 7, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 7, 13}, {3, 4, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30212 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4072 Fin15AnchoredAtom4074 Fin15AnchoredAtom4094
    Fin15AnchoredAtom4115 Fin15AnchoredAtom4255 Fin15AnchoredAtom4465 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 12, 14}, {3, 6, 7, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30213 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4073 Fin15AnchoredAtom4074 Fin15AnchoredAtom4095
    Fin15AnchoredAtom4116 Fin15AnchoredAtom4256 Fin15AnchoredAtom4466 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 7, 13, 14}, {3, 6, 7, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 7, 14}, {3, 4, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30214 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom4257 chi ∧
      Fin15AnchoredAtom4467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4075 Fin15AnchoredAtom4076 Fin15AnchoredAtom4081
    Fin15AnchoredAtom4117 Fin15AnchoredAtom4257 Fin15AnchoredAtom4467 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 9, 10}, {3, 6, 8, 9, 10}, {3, 4, 8, 9, 10}, {3, 4, 6, 9, 10}, {3, 4, 6, 8, 10}, {3, 4, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30215 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4075 chi ∧
      Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4121 chi ∧
      Fin15AnchoredAtom4261 chi ∧
      Fin15AnchoredAtom4471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4075 Fin15AnchoredAtom4080 Fin15AnchoredAtom4085
    Fin15AnchoredAtom4121 Fin15AnchoredAtom4261 Fin15AnchoredAtom4471 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 8, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 8, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 9, 14}, {3, 6, 8, 9, 14}, {3, 4, 8, 9, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 8, 14}, {3, 4, 6, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30216 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4079 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4076 Fin15AnchoredAtom4079 Fin15AnchoredAtom4088
    Fin15AnchoredAtom4124 Fin15AnchoredAtom4264 Fin15AnchoredAtom4474 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 10, 13}, {3, 6, 8, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 8, 13}, {3, 4, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30217 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4076 chi ∧
      Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4125 chi ∧
      Fin15AnchoredAtom4265 chi ∧
      Fin15AnchoredAtom4475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4076 Fin15AnchoredAtom4080 Fin15AnchoredAtom4089
    Fin15AnchoredAtom4125 Fin15AnchoredAtom4265 Fin15AnchoredAtom4475 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 8, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 8, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 10, 14}, {3, 6, 8, 10, 14}, {3, 4, 8, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 8, 14}, {3, 4, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30218 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4078 chi ∧
      Fin15AnchoredAtom4080 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4130 chi ∧
      Fin15AnchoredAtom4270 chi ∧
      Fin15AnchoredAtom4480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4078 Fin15AnchoredAtom4080 Fin15AnchoredAtom4094
    Fin15AnchoredAtom4130 Fin15AnchoredAtom4270 Fin15AnchoredAtom4480 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 8, 12, 14}, {3, 6, 8, 12, 14}, {3, 4, 8, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 8, 14}, {3, 4, 6, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30219 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4082 chi ∧
      Fin15AnchoredAtom4086 chi ∧
      Fin15AnchoredAtom4132 chi ∧
      Fin15AnchoredAtom4272 chi ∧
      Fin15AnchoredAtom4482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4081 Fin15AnchoredAtom4082 Fin15AnchoredAtom4086
    Fin15AnchoredAtom4132 Fin15AnchoredAtom4272 Fin15AnchoredAtom4482 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 9, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 9, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 11}, {3, 6, 9, 10, 11}, {3, 4, 9, 10, 11}, {3, 4, 6, 10, 11}, {3, 4, 6, 9, 11}, {3, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30220 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4081 Fin15AnchoredAtom4083 Fin15AnchoredAtom4087
    Fin15AnchoredAtom4133 Fin15AnchoredAtom4273 Fin15AnchoredAtom4483 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 6, 10, 12}, {3, 4, 6, 9, 12}, {3, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30221 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4081 Fin15AnchoredAtom4084 Fin15AnchoredAtom4088
    Fin15AnchoredAtom4134 Fin15AnchoredAtom4274 Fin15AnchoredAtom4484 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30222 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4081 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4081 Fin15AnchoredAtom4085 Fin15AnchoredAtom4089
    Fin15AnchoredAtom4135 Fin15AnchoredAtom4275 Fin15AnchoredAtom4485 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30223 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4083 Fin15AnchoredAtom4084 Fin15AnchoredAtom4093
    Fin15AnchoredAtom4139 Fin15AnchoredAtom4279 Fin15AnchoredAtom4489 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 9, 13}, {3, 4, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30224 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4083 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4083 Fin15AnchoredAtom4085 Fin15AnchoredAtom4094
    Fin15AnchoredAtom4140 Fin15AnchoredAtom4280 Fin15AnchoredAtom4490 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30225 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4084 chi ∧
      Fin15AnchoredAtom4085 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4084 Fin15AnchoredAtom4085 Fin15AnchoredAtom4095
    Fin15AnchoredAtom4141 Fin15AnchoredAtom4281 Fin15AnchoredAtom4491 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 9, 14}, {3, 4, 6, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30226 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4087 Fin15AnchoredAtom4088 Fin15AnchoredAtom4093
    Fin15AnchoredAtom4145 Fin15AnchoredAtom4285 Fin15AnchoredAtom4495 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 6, 12, 13}, {3, 4, 6, 10, 13}, {3, 4, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30227 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4087 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4087 Fin15AnchoredAtom4089 Fin15AnchoredAtom4094
    Fin15AnchoredAtom4146 Fin15AnchoredAtom4286 Fin15AnchoredAtom4496 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30228 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4088 chi ∧
      Fin15AnchoredAtom4089 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4088 Fin15AnchoredAtom4089 Fin15AnchoredAtom4095
    Fin15AnchoredAtom4147 Fin15AnchoredAtom4287 Fin15AnchoredAtom4497 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 10, 14}, {3, 4, 6, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30229 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4093 chi ∧
      Fin15AnchoredAtom4094 chi ∧
      Fin15AnchoredAtom4095 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4093 Fin15AnchoredAtom4094 Fin15AnchoredAtom4095
    Fin15AnchoredAtom4151 Fin15AnchoredAtom4291 Fin15AnchoredAtom4501 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 6, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 6, 13, 14}, {3, 4, 6, 12, 14}, {3, 4, 6, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30230 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4096 chi ∧
      Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom4292 chi ∧
      Fin15AnchoredAtom4502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4096 Fin15AnchoredAtom4097 Fin15AnchoredAtom4102
    Fin15AnchoredAtom4117 Fin15AnchoredAtom4292 Fin15AnchoredAtom4502 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 9, 10}, {3, 7, 8, 9, 10}, {3, 4, 8, 9, 10}, {3, 4, 7, 9, 10}, {3, 4, 7, 8, 10}, {3, 4, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30231 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4097 chi ∧
      Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4299 chi ∧
      Fin15AnchoredAtom4509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4097 Fin15AnchoredAtom4100 Fin15AnchoredAtom4109
    Fin15AnchoredAtom4124 Fin15AnchoredAtom4299 Fin15AnchoredAtom4509 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 10, 13}, {3, 7, 8, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30232 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4129 chi ∧
      Fin15AnchoredAtom4304 chi ∧
      Fin15AnchoredAtom4514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4099 Fin15AnchoredAtom4100 Fin15AnchoredAtom4114
    Fin15AnchoredAtom4129 Fin15AnchoredAtom4304 Fin15AnchoredAtom4514 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 12, 13}, {3, 7, 8, 12, 13}, {3, 4, 8, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 8, 13}, {3, 4, 7, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30233 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4099 chi ∧
      Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4130 chi ∧
      Fin15AnchoredAtom4305 chi ∧
      Fin15AnchoredAtom4515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4099 Fin15AnchoredAtom4101 Fin15AnchoredAtom4115
    Fin15AnchoredAtom4130 Fin15AnchoredAtom4305 Fin15AnchoredAtom4515 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 8, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 8, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 12, 14}, {3, 7, 8, 12, 14}, {3, 4, 8, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30234 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4100 chi ∧
      Fin15AnchoredAtom4101 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4131 chi ∧
      Fin15AnchoredAtom4306 chi ∧
      Fin15AnchoredAtom4516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4100 Fin15AnchoredAtom4101 Fin15AnchoredAtom4116
    Fin15AnchoredAtom4131 Fin15AnchoredAtom4306 Fin15AnchoredAtom4516 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 8, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 8, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 8, 13, 14}, {3, 7, 8, 13, 14}, {3, 4, 8, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 8, 14}, {3, 4, 7, 8, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30235 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4102 Fin15AnchoredAtom4104 Fin15AnchoredAtom4108
    Fin15AnchoredAtom4133 Fin15AnchoredAtom4308 Fin15AnchoredAtom4518 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 4, 9, 10, 12}, {3, 4, 7, 10, 12}, {3, 4, 7, 9, 12}, {3, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30236 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4102 Fin15AnchoredAtom4105 Fin15AnchoredAtom4109
    Fin15AnchoredAtom4134 Fin15AnchoredAtom4309 Fin15AnchoredAtom4519 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30237 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4102 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4102 Fin15AnchoredAtom4106 Fin15AnchoredAtom4110
    Fin15AnchoredAtom4135 Fin15AnchoredAtom4310 Fin15AnchoredAtom4520 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 4, 9, 10, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30238 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4104 Fin15AnchoredAtom4105 Fin15AnchoredAtom4114
    Fin15AnchoredAtom4139 Fin15AnchoredAtom4314 Fin15AnchoredAtom4524 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 9, 13}, {3, 4, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30239 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4104 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4104 Fin15AnchoredAtom4106 Fin15AnchoredAtom4115
    Fin15AnchoredAtom4140 Fin15AnchoredAtom4315 Fin15AnchoredAtom4525 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30240 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4105 chi ∧
      Fin15AnchoredAtom4106 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4105 Fin15AnchoredAtom4106 Fin15AnchoredAtom4116
    Fin15AnchoredAtom4141 Fin15AnchoredAtom4316 Fin15AnchoredAtom4526 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 9, 14}, {3, 4, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30241 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4108 Fin15AnchoredAtom4109 Fin15AnchoredAtom4114
    Fin15AnchoredAtom4145 Fin15AnchoredAtom4320 Fin15AnchoredAtom4530 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 7, 12, 13}, {3, 4, 7, 10, 13}, {3, 4, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30242 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4108 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4108 Fin15AnchoredAtom4110 Fin15AnchoredAtom4115
    Fin15AnchoredAtom4146 Fin15AnchoredAtom4321 Fin15AnchoredAtom4531 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30243 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4109 chi ∧
      Fin15AnchoredAtom4110 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4109 Fin15AnchoredAtom4110 Fin15AnchoredAtom4116
    Fin15AnchoredAtom4147 Fin15AnchoredAtom4322 Fin15AnchoredAtom4532 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 10, 14}, {3, 4, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30244 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4114 chi ∧
      Fin15AnchoredAtom4115 chi ∧
      Fin15AnchoredAtom4116 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4536 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4114 Fin15AnchoredAtom4115 Fin15AnchoredAtom4116
    Fin15AnchoredAtom4151 Fin15AnchoredAtom4326 Fin15AnchoredAtom4536 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 7, 13, 14}, {3, 4, 7, 12, 14}, {3, 4, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30245 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4117 chi ∧
      Fin15AnchoredAtom4120 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4329 chi ∧
      Fin15AnchoredAtom4539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4117 Fin15AnchoredAtom4120 Fin15AnchoredAtom4124
    Fin15AnchoredAtom4134 Fin15AnchoredAtom4329 Fin15AnchoredAtom4539 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 9, 10, 13}, {3, 8, 9, 10, 13}, {3, 4, 9, 10, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 9, 13}, {3, 4, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30246 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4123 chi ∧
      Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4129 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4340 chi ∧
      Fin15AnchoredAtom4550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4123 Fin15AnchoredAtom4124 Fin15AnchoredAtom4129
    Fin15AnchoredAtom4145 Fin15AnchoredAtom4340 Fin15AnchoredAtom4550 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 8, 12, 13}, {3, 4, 8, 10, 13}, {3, 4, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30247 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4123 chi ∧
      Fin15AnchoredAtom4125 chi ∧
      Fin15AnchoredAtom4130 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4341 chi ∧
      Fin15AnchoredAtom4551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4123 Fin15AnchoredAtom4125 Fin15AnchoredAtom4130
    Fin15AnchoredAtom4146 Fin15AnchoredAtom4341 Fin15AnchoredAtom4551 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 10, 12, 14}, {3, 8, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 8, 12, 14}, {3, 4, 8, 10, 14}, {3, 4, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30248 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4124 chi ∧
      Fin15AnchoredAtom4125 chi ∧
      Fin15AnchoredAtom4131 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4342 chi ∧
      Fin15AnchoredAtom4552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4124 Fin15AnchoredAtom4125 Fin15AnchoredAtom4131
    Fin15AnchoredAtom4147 Fin15AnchoredAtom4342 Fin15AnchoredAtom4552 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 8, 10, 13, 14}, {3, 8, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 8, 13, 14}, {3, 4, 8, 10, 14}, {3, 4, 8, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30249 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4133 Fin15AnchoredAtom4134 Fin15AnchoredAtom4139
    Fin15AnchoredAtom4145 Fin15AnchoredAtom4350 Fin15AnchoredAtom4560 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 4, 10, 12, 13}, {3, 4, 9, 12, 13}, {3, 4, 9, 10, 13}, {3, 4, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30250 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4133 Fin15AnchoredAtom4135 Fin15AnchoredAtom4140
    Fin15AnchoredAtom4146 Fin15AnchoredAtom4351 Fin15AnchoredAtom4561 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 4, 10, 12, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30251 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4134 Fin15AnchoredAtom4135 Fin15AnchoredAtom4141
    Fin15AnchoredAtom4147 Fin15AnchoredAtom4352 Fin15AnchoredAtom4562 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 10, 14}, {3, 4, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30252 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4139 Fin15AnchoredAtom4140 Fin15AnchoredAtom4141
    Fin15AnchoredAtom4151 Fin15AnchoredAtom4356 Fin15AnchoredAtom4566 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 9, 13, 14}, {3, 4, 9, 12, 14}, {3, 4, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30253 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4145 Fin15AnchoredAtom4146 Fin15AnchoredAtom4147
    Fin15AnchoredAtom4151 Fin15AnchoredAtom4360 Fin15AnchoredAtom4570 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 4, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 4, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{4, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 4, 12, 13, 14}, {3, 4, 10, 13, 14}, {3, 4, 10, 12, 14}, {3, 4, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30254 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4153 Fin15AnchoredAtom4154 Fin15AnchoredAtom4165
    Fin15AnchoredAtom4186 Fin15AnchoredAtom4242 Fin15AnchoredAtom4578 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {3, 6, 7, 9, 10}, {3, 5, 7, 9, 10}, {3, 5, 6, 9, 10}, {3, 5, 6, 7, 10}, {3, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30255 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4153 Fin15AnchoredAtom4156 Fin15AnchoredAtom4167
    Fin15AnchoredAtom4188 Fin15AnchoredAtom4244 Fin15AnchoredAtom4580 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {3, 6, 7, 9, 12}, {3, 5, 7, 9, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30256 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4581 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4153 Fin15AnchoredAtom4157 Fin15AnchoredAtom4168
    Fin15AnchoredAtom4189 Fin15AnchoredAtom4245 Fin15AnchoredAtom4581 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {3, 6, 7, 9, 13}, {3, 5, 7, 9, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30257 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4153 Fin15AnchoredAtom4158 Fin15AnchoredAtom4169
    Fin15AnchoredAtom4190 Fin15AnchoredAtom4246 Fin15AnchoredAtom4582 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {3, 6, 7, 9, 14}, {3, 5, 7, 9, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30258 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4155 chi ∧
      Fin15AnchoredAtom4170 chi ∧
      Fin15AnchoredAtom4191 chi ∧
      Fin15AnchoredAtom4247 chi ∧
      Fin15AnchoredAtom4583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4154 Fin15AnchoredAtom4155 Fin15AnchoredAtom4170
    Fin15AnchoredAtom4191 Fin15AnchoredAtom4247 Fin15AnchoredAtom4583 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 10, 11}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 10, 11} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 11}, {3, 6, 7, 10, 11}, {3, 5, 7, 10, 11}, {3, 5, 6, 10, 11}, {3, 5, 6, 7, 11}, {3, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30259 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4154 Fin15AnchoredAtom4156 Fin15AnchoredAtom4171
    Fin15AnchoredAtom4192 Fin15AnchoredAtom4248 Fin15AnchoredAtom4584 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {3, 6, 7, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 7, 12}, {3, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30260 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4154 Fin15AnchoredAtom4157 Fin15AnchoredAtom4172
    Fin15AnchoredAtom4193 Fin15AnchoredAtom4249 Fin15AnchoredAtom4585 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {3, 6, 7, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30261 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4154 Fin15AnchoredAtom4158 Fin15AnchoredAtom4173
    Fin15AnchoredAtom4194 Fin15AnchoredAtom4250 Fin15AnchoredAtom4586 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {3, 6, 7, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30262 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4156 Fin15AnchoredAtom4157 Fin15AnchoredAtom4177
    Fin15AnchoredAtom4198 Fin15AnchoredAtom4254 Fin15AnchoredAtom4590 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {3, 6, 7, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 7, 13}, {3, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30263 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4156 Fin15AnchoredAtom4158 Fin15AnchoredAtom4178
    Fin15AnchoredAtom4199 Fin15AnchoredAtom4255 Fin15AnchoredAtom4591 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {3, 6, 7, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30264 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4157 Fin15AnchoredAtom4158 Fin15AnchoredAtom4179
    Fin15AnchoredAtom4200 Fin15AnchoredAtom4256 Fin15AnchoredAtom4592 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {3, 6, 7, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 7, 14}, {3, 5, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30265 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4160 chi ∧
      Fin15AnchoredAtom4163 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4160 Fin15AnchoredAtom4163 Fin15AnchoredAtom4172
    Fin15AnchoredAtom4208 Fin15AnchoredAtom4264 Fin15AnchoredAtom4600 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 8, 10, 13}, {3, 6, 8, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 8, 13}, {3, 5, 6, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30266 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4165 Fin15AnchoredAtom4167 Fin15AnchoredAtom4171
    Fin15AnchoredAtom4217 Fin15AnchoredAtom4273 Fin15AnchoredAtom4609 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 6, 10, 12}, {3, 5, 6, 9, 12}, {3, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30267 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4165 Fin15AnchoredAtom4168 Fin15AnchoredAtom4172
    Fin15AnchoredAtom4218 Fin15AnchoredAtom4274 Fin15AnchoredAtom4610 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30268 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4165 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4165 Fin15AnchoredAtom4169 Fin15AnchoredAtom4173
    Fin15AnchoredAtom4219 Fin15AnchoredAtom4275 Fin15AnchoredAtom4611 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30269 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4167 Fin15AnchoredAtom4168 Fin15AnchoredAtom4177
    Fin15AnchoredAtom4223 Fin15AnchoredAtom4279 Fin15AnchoredAtom4615 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 9, 13}, {3, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30270 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4167 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4167 Fin15AnchoredAtom4169 Fin15AnchoredAtom4178
    Fin15AnchoredAtom4224 Fin15AnchoredAtom4280 Fin15AnchoredAtom4616 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30271 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4168 chi ∧
      Fin15AnchoredAtom4169 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4168 Fin15AnchoredAtom4169 Fin15AnchoredAtom4179
    Fin15AnchoredAtom4225 Fin15AnchoredAtom4281 Fin15AnchoredAtom4617 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 9, 14}, {3, 5, 6, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30272 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4171 Fin15AnchoredAtom4172 Fin15AnchoredAtom4177
    Fin15AnchoredAtom4229 Fin15AnchoredAtom4285 Fin15AnchoredAtom4621 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 6, 12, 13}, {3, 5, 6, 10, 13}, {3, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30273 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4171 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4171 Fin15AnchoredAtom4173 Fin15AnchoredAtom4178
    Fin15AnchoredAtom4230 Fin15AnchoredAtom4286 Fin15AnchoredAtom4622 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30274 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4172 chi ∧
      Fin15AnchoredAtom4173 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4172 Fin15AnchoredAtom4173 Fin15AnchoredAtom4179
    Fin15AnchoredAtom4231 Fin15AnchoredAtom4287 Fin15AnchoredAtom4623 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 10, 14}, {3, 5, 6, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30275 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4177 chi ∧
      Fin15AnchoredAtom4178 chi ∧
      Fin15AnchoredAtom4179 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4177 Fin15AnchoredAtom4178 Fin15AnchoredAtom4179
    Fin15AnchoredAtom4235 Fin15AnchoredAtom4291 Fin15AnchoredAtom4627 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 6, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 6, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 6, 13, 14}, {3, 5, 6, 12, 14}, {3, 5, 6, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30276 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4180 chi ∧
      Fin15AnchoredAtom4181 chi ∧
      Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4201 chi ∧
      Fin15AnchoredAtom4292 chi ∧
      Fin15AnchoredAtom4628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4180 Fin15AnchoredAtom4181 Fin15AnchoredAtom4186
    Fin15AnchoredAtom4201 Fin15AnchoredAtom4292 Fin15AnchoredAtom4628 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 8, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 8, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 9, 10}, {3, 7, 8, 9, 10}, {3, 5, 8, 9, 10}, {3, 5, 7, 9, 10}, {3, 5, 7, 8, 10}, {3, 5, 7, 8, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30277 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4181 chi ∧
      Fin15AnchoredAtom4184 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom4299 chi ∧
      Fin15AnchoredAtom4635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4181 Fin15AnchoredAtom4184 Fin15AnchoredAtom4193
    Fin15AnchoredAtom4208 Fin15AnchoredAtom4299 Fin15AnchoredAtom4635 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 10, 13}, {3, 7, 8, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30278 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4183 chi ∧
      Fin15AnchoredAtom4184 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4213 chi ∧
      Fin15AnchoredAtom4304 chi ∧
      Fin15AnchoredAtom4640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4183 Fin15AnchoredAtom4184 Fin15AnchoredAtom4198
    Fin15AnchoredAtom4213 Fin15AnchoredAtom4304 Fin15AnchoredAtom4640 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 8, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 8, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 8, 12, 13}, {3, 7, 8, 12, 13}, {3, 5, 8, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 8, 13}, {3, 5, 7, 8, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30279 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4186 Fin15AnchoredAtom4188 Fin15AnchoredAtom4192
    Fin15AnchoredAtom4217 Fin15AnchoredAtom4308 Fin15AnchoredAtom4644 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 5, 9, 10, 12}, {3, 5, 7, 10, 12}, {3, 5, 7, 9, 12}, {3, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30280 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4186 Fin15AnchoredAtom4189 Fin15AnchoredAtom4193
    Fin15AnchoredAtom4218 Fin15AnchoredAtom4309 Fin15AnchoredAtom4645 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30281 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4186 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4186 Fin15AnchoredAtom4190 Fin15AnchoredAtom4194
    Fin15AnchoredAtom4219 Fin15AnchoredAtom4310 Fin15AnchoredAtom4646 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 5, 9, 10, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30282 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4188 Fin15AnchoredAtom4189 Fin15AnchoredAtom4198
    Fin15AnchoredAtom4223 Fin15AnchoredAtom4314 Fin15AnchoredAtom4650 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 9, 13}, {3, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30283 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4188 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4188 Fin15AnchoredAtom4190 Fin15AnchoredAtom4199
    Fin15AnchoredAtom4224 Fin15AnchoredAtom4315 Fin15AnchoredAtom4651 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30284 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4189 chi ∧
      Fin15AnchoredAtom4190 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4189 Fin15AnchoredAtom4190 Fin15AnchoredAtom4200
    Fin15AnchoredAtom4225 Fin15AnchoredAtom4316 Fin15AnchoredAtom4652 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 9, 14}, {3, 5, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30285 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4192 Fin15AnchoredAtom4193 Fin15AnchoredAtom4198
    Fin15AnchoredAtom4229 Fin15AnchoredAtom4320 Fin15AnchoredAtom4656 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 7, 12, 13}, {3, 5, 7, 10, 13}, {3, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30286 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4192 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4192 Fin15AnchoredAtom4194 Fin15AnchoredAtom4199
    Fin15AnchoredAtom4230 Fin15AnchoredAtom4321 Fin15AnchoredAtom4657 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30287 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4193 chi ∧
      Fin15AnchoredAtom4194 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4193 Fin15AnchoredAtom4194 Fin15AnchoredAtom4200
    Fin15AnchoredAtom4231 Fin15AnchoredAtom4322 Fin15AnchoredAtom4658 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 10, 14}, {3, 5, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30288 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4198 chi ∧
      Fin15AnchoredAtom4199 chi ∧
      Fin15AnchoredAtom4200 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4198 Fin15AnchoredAtom4199 Fin15AnchoredAtom4200
    Fin15AnchoredAtom4235 Fin15AnchoredAtom4326 Fin15AnchoredAtom4662 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 7, 13, 14}, {3, 5, 7, 12, 14}, {3, 5, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30289 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4201 chi ∧
      Fin15AnchoredAtom4204 chi ∧
      Fin15AnchoredAtom4208 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4329 chi ∧
      Fin15AnchoredAtom4665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4201 Fin15AnchoredAtom4204 Fin15AnchoredAtom4208
    Fin15AnchoredAtom4218 Fin15AnchoredAtom4329 Fin15AnchoredAtom4665 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 8, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 8, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 8, 9, 10, 13}, {3, 8, 9, 10, 13}, {3, 5, 9, 10, 13}, {3, 5, 8, 10, 13}, {3, 5, 8, 9, 13}, {3, 5, 8, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30290 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4217 Fin15AnchoredAtom4218 Fin15AnchoredAtom4223
    Fin15AnchoredAtom4229 Fin15AnchoredAtom4350 Fin15AnchoredAtom4686 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 5, 10, 12, 13}, {3, 5, 9, 12, 13}, {3, 5, 9, 10, 13}, {3, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30291 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4217 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4217 Fin15AnchoredAtom4219 Fin15AnchoredAtom4224
    Fin15AnchoredAtom4230 Fin15AnchoredAtom4351 Fin15AnchoredAtom4687 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 5, 10, 12, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30292 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4218 chi ∧
      Fin15AnchoredAtom4219 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4218 Fin15AnchoredAtom4219 Fin15AnchoredAtom4225
    Fin15AnchoredAtom4231 Fin15AnchoredAtom4352 Fin15AnchoredAtom4688 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 10, 14}, {3, 5, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30293 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4223 chi ∧
      Fin15AnchoredAtom4224 chi ∧
      Fin15AnchoredAtom4225 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4223 Fin15AnchoredAtom4224 Fin15AnchoredAtom4225
    Fin15AnchoredAtom4235 Fin15AnchoredAtom4356 Fin15AnchoredAtom4692 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 9, 13, 14}, {3, 5, 9, 12, 14}, {3, 5, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30294 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4229 chi ∧
      Fin15AnchoredAtom4230 chi ∧
      Fin15AnchoredAtom4231 chi ∧
      Fin15AnchoredAtom4235 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4229 Fin15AnchoredAtom4230 Fin15AnchoredAtom4231
    Fin15AnchoredAtom4235 Fin15AnchoredAtom4360 Fin15AnchoredAtom4696 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 5, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 5, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 5, 12, 13, 14}, {3, 5, 10, 13, 14}, {3, 5, 10, 12, 14}, {3, 5, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30295 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4237 chi ∧
      Fin15AnchoredAtom4239 chi ∧
      Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4263 chi ∧
      Fin15AnchoredAtom4298 chi ∧
      Fin15AnchoredAtom4704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4237 Fin15AnchoredAtom4239 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4263 Fin15AnchoredAtom4298 Fin15AnchoredAtom4704 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 8, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 8, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 12}, {3, 7, 8, 10, 12}, {3, 6, 8, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 8, 12}, {3, 6, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30296 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4237 chi ∧
      Fin15AnchoredAtom4240 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4299 chi ∧
      Fin15AnchoredAtom4705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4237 Fin15AnchoredAtom4240 Fin15AnchoredAtom4249
    Fin15AnchoredAtom4264 Fin15AnchoredAtom4299 Fin15AnchoredAtom4705 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 8, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 8, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 8, 10, 13}, {3, 7, 8, 10, 13}, {3, 6, 8, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 8, 13}, {3, 6, 7, 8, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30297 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4242 Fin15AnchoredAtom4244 Fin15AnchoredAtom4248
    Fin15AnchoredAtom4273 Fin15AnchoredAtom4308 Fin15AnchoredAtom4714 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 9, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 9, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 12}, {3, 7, 9, 10, 12}, {3, 6, 9, 10, 12}, {3, 6, 7, 10, 12}, {3, 6, 7, 9, 12}, {3, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30298 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4242 Fin15AnchoredAtom4245 Fin15AnchoredAtom4249
    Fin15AnchoredAtom4274 Fin15AnchoredAtom4309 Fin15AnchoredAtom4715 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 9, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 9, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 13}, {3, 7, 9, 10, 13}, {3, 6, 9, 10, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30299 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4242 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4242 Fin15AnchoredAtom4246 Fin15AnchoredAtom4250
    Fin15AnchoredAtom4275 Fin15AnchoredAtom4310 Fin15AnchoredAtom4716 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 9, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 9, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 10, 14}, {3, 7, 9, 10, 14}, {3, 6, 9, 10, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30300 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4244 Fin15AnchoredAtom4245 Fin15AnchoredAtom4254
    Fin15AnchoredAtom4279 Fin15AnchoredAtom4314 Fin15AnchoredAtom4720 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 9, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 9, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 13}, {3, 7, 9, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 9, 13}, {3, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30301 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4244 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4244 Fin15AnchoredAtom4246 Fin15AnchoredAtom4255
    Fin15AnchoredAtom4280 Fin15AnchoredAtom4315 Fin15AnchoredAtom4721 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 9, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 9, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 12, 14}, {3, 7, 9, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30302 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4245 chi ∧
      Fin15AnchoredAtom4246 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4245 Fin15AnchoredAtom4246 Fin15AnchoredAtom4256
    Fin15AnchoredAtom4281 Fin15AnchoredAtom4316 Fin15AnchoredAtom4722 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 9, 14}, {3, 6, 7, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30303 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4248 Fin15AnchoredAtom4249 Fin15AnchoredAtom4254
    Fin15AnchoredAtom4285 Fin15AnchoredAtom4320 Fin15AnchoredAtom4726 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 7, 12, 13}, {3, 6, 7, 10, 13}, {3, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30304 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4248 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4248 Fin15AnchoredAtom4250 Fin15AnchoredAtom4255
    Fin15AnchoredAtom4286 Fin15AnchoredAtom4321 Fin15AnchoredAtom4727 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30305 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4249 chi ∧
      Fin15AnchoredAtom4250 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4249 Fin15AnchoredAtom4250 Fin15AnchoredAtom4256
    Fin15AnchoredAtom4287 Fin15AnchoredAtom4322 Fin15AnchoredAtom4728 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 10, 14}, {3, 6, 7, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30306 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4254 chi ∧
      Fin15AnchoredAtom4255 chi ∧
      Fin15AnchoredAtom4256 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4254 Fin15AnchoredAtom4255 Fin15AnchoredAtom4256
    Fin15AnchoredAtom4291 Fin15AnchoredAtom4326 Fin15AnchoredAtom4732 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 7, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 7, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 7, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 7, 13, 14}, {3, 6, 7, 12, 14}, {3, 6, 7, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30307 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4263 chi ∧
      Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4269 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4340 chi ∧
      Fin15AnchoredAtom4746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4263 Fin15AnchoredAtom4264 Fin15AnchoredAtom4269
    Fin15AnchoredAtom4285 Fin15AnchoredAtom4340 Fin15AnchoredAtom4746 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 8, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 8, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 13}, {3, 8, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 8, 12, 13}, {3, 6, 8, 10, 13}, {3, 6, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30308 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4263 chi ∧
      Fin15AnchoredAtom4265 chi ∧
      Fin15AnchoredAtom4270 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4341 chi ∧
      Fin15AnchoredAtom4747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4263 Fin15AnchoredAtom4265 Fin15AnchoredAtom4270
    Fin15AnchoredAtom4286 Fin15AnchoredAtom4341 Fin15AnchoredAtom4747 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 8, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 8, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 12, 14}, {3, 8, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 8, 12, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30309 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4264 chi ∧
      Fin15AnchoredAtom4265 chi ∧
      Fin15AnchoredAtom4271 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4342 chi ∧
      Fin15AnchoredAtom4748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4264 Fin15AnchoredAtom4265 Fin15AnchoredAtom4271
    Fin15AnchoredAtom4287 Fin15AnchoredAtom4342 Fin15AnchoredAtom4748 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 8, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 8, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 8, 10, 13, 14}, {3, 8, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 8, 13, 14}, {3, 6, 8, 10, 14}, {3, 6, 8, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30310 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4272 chi ∧
      Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4276 chi ∧
      Fin15AnchoredAtom4282 chi ∧
      Fin15AnchoredAtom4347 chi ∧
      Fin15AnchoredAtom4753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4272 Fin15AnchoredAtom4273 Fin15AnchoredAtom4276
    Fin15AnchoredAtom4282 Fin15AnchoredAtom4347 Fin15AnchoredAtom4753 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 9, 10, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 9, 10, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 11, 12}, {3, 9, 10, 11, 12}, {3, 6, 10, 11, 12}, {3, 6, 9, 11, 12}, {3, 6, 9, 10, 12}, {3, 6, 9, 10, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30311 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4273 Fin15AnchoredAtom4274 Fin15AnchoredAtom4279
    Fin15AnchoredAtom4285 Fin15AnchoredAtom4350 Fin15AnchoredAtom4756 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 6, 10, 12, 13}, {3, 6, 9, 12, 13}, {3, 6, 9, 10, 13}, {3, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30312 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4273 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4273 Fin15AnchoredAtom4275 Fin15AnchoredAtom4280
    Fin15AnchoredAtom4286 Fin15AnchoredAtom4351 Fin15AnchoredAtom4757 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 6, 10, 12, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30313 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4274 chi ∧
      Fin15AnchoredAtom4275 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4274 Fin15AnchoredAtom4275 Fin15AnchoredAtom4281
    Fin15AnchoredAtom4287 Fin15AnchoredAtom4352 Fin15AnchoredAtom4758 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 10, 14}, {3, 6, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30314 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4279 chi ∧
      Fin15AnchoredAtom4280 chi ∧
      Fin15AnchoredAtom4281 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4279 Fin15AnchoredAtom4280 Fin15AnchoredAtom4281
    Fin15AnchoredAtom4291 Fin15AnchoredAtom4356 Fin15AnchoredAtom4762 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 9, 13, 14}, {3, 6, 9, 12, 14}, {3, 6, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30315 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4285 chi ∧
      Fin15AnchoredAtom4286 chi ∧
      Fin15AnchoredAtom4287 chi ∧
      Fin15AnchoredAtom4291 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4285 Fin15AnchoredAtom4286 Fin15AnchoredAtom4287
    Fin15AnchoredAtom4291 Fin15AnchoredAtom4360 Fin15AnchoredAtom4766 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 6, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 6, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{6, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 6, 12, 13, 14}, {3, 6, 10, 13, 14}, {3, 6, 10, 12, 14}, {3, 6, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30316 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4295 chi ∧
      Fin15AnchoredAtom4296 chi ∧
      Fin15AnchoredAtom4306 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4336 chi ∧
      Fin15AnchoredAtom4777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4295 Fin15AnchoredAtom4296 Fin15AnchoredAtom4306
    Fin15AnchoredAtom4316 Fin15AnchoredAtom4336 Fin15AnchoredAtom4777 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 7, 8, 9, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 7, 8, 9, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 8, 9, 13, 14}, {3, 8, 9, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 8, 13, 14}, {3, 7, 8, 9, 14}, {3, 7, 8, 9, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30317 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4308 Fin15AnchoredAtom4309 Fin15AnchoredAtom4314
    Fin15AnchoredAtom4320 Fin15AnchoredAtom4350 Fin15AnchoredAtom4791 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 7, 9, 10, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 7, 9, 10, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 13}, {3, 9, 10, 12, 13}, {3, 7, 10, 12, 13}, {3, 7, 9, 12, 13}, {3, 7, 9, 10, 13}, {3, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30318 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4308 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4308 Fin15AnchoredAtom4310 Fin15AnchoredAtom4315
    Fin15AnchoredAtom4321 Fin15AnchoredAtom4351 Fin15AnchoredAtom4792 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 7, 9, 10, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 7, 9, 10, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 12, 14}, {3, 9, 10, 12, 14}, {3, 7, 10, 12, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30319 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4309 chi ∧
      Fin15AnchoredAtom4310 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4309 Fin15AnchoredAtom4310 Fin15AnchoredAtom4316
    Fin15AnchoredAtom4322 Fin15AnchoredAtom4352 Fin15AnchoredAtom4793 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 7, 9, 10, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 7, 9, 10, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 10, 13, 14}, {3, 9, 10, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 10, 14}, {3, 7, 9, 10, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30320 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4314 chi ∧
      Fin15AnchoredAtom4315 chi ∧
      Fin15AnchoredAtom4316 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4314 Fin15AnchoredAtom4315 Fin15AnchoredAtom4316
    Fin15AnchoredAtom4326 Fin15AnchoredAtom4356 Fin15AnchoredAtom4797 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 7, 9, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 7, 9, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 9, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 9, 13, 14}, {3, 7, 9, 12, 14}, {3, 7, 9, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30321 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4320 chi ∧
      Fin15AnchoredAtom4321 chi ∧
      Fin15AnchoredAtom4322 chi ∧
      Fin15AnchoredAtom4326 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4320 Fin15AnchoredAtom4321 Fin15AnchoredAtom4322
    Fin15AnchoredAtom4326 Fin15AnchoredAtom4360 Fin15AnchoredAtom4801 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 7, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 7, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{7, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 7, 12, 13, 14}, {3, 7, 10, 13, 14}, {3, 7, 10, 12, 14}, {3, 7, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30322 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4350 chi ∧
      Fin15AnchoredAtom4351 chi ∧
      Fin15AnchoredAtom4352 chi ∧
      Fin15AnchoredAtom4356 chi ∧
      Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom4821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4350 Fin15AnchoredAtom4351 Fin15AnchoredAtom4352
    Fin15AnchoredAtom4356 Fin15AnchoredAtom4360 Fin15AnchoredAtom4821 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{3, 9, 10, 12, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({3, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({3, 9, 10, 12, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{9, 10, 12, 13, 14}, {3, 10, 12, 13, 14}, {3, 9, 12, 13, 14}, {3, 9, 10, 13, 14}, {3, 9, 10, 12, 14}, {3, 9, 10, 12, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30323 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4362 chi ∧
      Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4369 chi ∧
      Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom4446 chi ∧
      Fin15AnchoredAtom4572 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4362 Fin15AnchoredAtom4363 Fin15AnchoredAtom4369
    Fin15AnchoredAtom4390 Fin15AnchoredAtom4446 Fin15AnchoredAtom4572 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 8, 9}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 8, 9} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 8, 9}, {4, 6, 7, 8, 9}, {4, 5, 7, 8, 9}, {4, 5, 6, 8, 9}, {4, 5, 6, 7, 9}, {4, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30324 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4362 chi ∧
      Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom4447 chi ∧
      Fin15AnchoredAtom4573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4362 Fin15AnchoredAtom4364 Fin15AnchoredAtom4370
    Fin15AnchoredAtom4391 Fin15AnchoredAtom4447 Fin15AnchoredAtom4573 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 8, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 8, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 8, 10}, {4, 6, 7, 8, 10}, {4, 5, 7, 8, 10}, {4, 5, 6, 8, 10}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 8}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30325 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom4452 chi ∧
      Fin15AnchoredAtom4578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4363 Fin15AnchoredAtom4364 Fin15AnchoredAtom4375
    Fin15AnchoredAtom4396 Fin15AnchoredAtom4452 Fin15AnchoredAtom4578 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 9, 10}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 9, 10} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 10}, {4, 6, 7, 9, 10}, {4, 5, 7, 9, 10}, {4, 5, 6, 9, 10}, {4, 5, 6, 7, 10}, {4, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30326 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom4454 chi ∧
      Fin15AnchoredAtom4580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4363 Fin15AnchoredAtom4366 Fin15AnchoredAtom4377
    Fin15AnchoredAtom4398 Fin15AnchoredAtom4454 Fin15AnchoredAtom4580 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 9, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 9, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 12}, {4, 6, 7, 9, 12}, {4, 5, 7, 9, 12}, {4, 5, 6, 9, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30327 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom4455 chi ∧
      Fin15AnchoredAtom4581 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4363 Fin15AnchoredAtom4367 Fin15AnchoredAtom4378
    Fin15AnchoredAtom4399 Fin15AnchoredAtom4455 Fin15AnchoredAtom4581 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 9, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 9, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 13}, {4, 6, 7, 9, 13}, {4, 5, 7, 9, 13}, {4, 5, 6, 9, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30328 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom4456 chi ∧
      Fin15AnchoredAtom4582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4363 Fin15AnchoredAtom4368 Fin15AnchoredAtom4379
    Fin15AnchoredAtom4400 Fin15AnchoredAtom4456 Fin15AnchoredAtom4582 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 9, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 9, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 9, 14}, {4, 6, 7, 9, 14}, {4, 5, 7, 9, 14}, {4, 5, 6, 9, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 9}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30329 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom4458 chi ∧
      Fin15AnchoredAtom4584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4364 Fin15AnchoredAtom4366 Fin15AnchoredAtom4381
    Fin15AnchoredAtom4402 Fin15AnchoredAtom4458 Fin15AnchoredAtom4584 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 10, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 10, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 12}, {4, 6, 7, 10, 12}, {4, 5, 7, 10, 12}, {4, 5, 6, 10, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30330 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom4459 chi ∧
      Fin15AnchoredAtom4585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4364 Fin15AnchoredAtom4367 Fin15AnchoredAtom4382
    Fin15AnchoredAtom4403 Fin15AnchoredAtom4459 Fin15AnchoredAtom4585 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 10, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 10, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 13}, {4, 6, 7, 10, 13}, {4, 5, 7, 10, 13}, {4, 5, 6, 10, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30331 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom4460 chi ∧
      Fin15AnchoredAtom4586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4364 Fin15AnchoredAtom4368 Fin15AnchoredAtom4383
    Fin15AnchoredAtom4404 Fin15AnchoredAtom4460 Fin15AnchoredAtom4586 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 10, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 10, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 10, 14}, {4, 6, 7, 10, 14}, {4, 5, 7, 10, 14}, {4, 5, 6, 10, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 10}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30332 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4365 chi ∧
      Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4384 chi ∧
      Fin15AnchoredAtom4405 chi ∧
      Fin15AnchoredAtom4461 chi ∧
      Fin15AnchoredAtom4587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4365 Fin15AnchoredAtom4366 Fin15AnchoredAtom4384
    Fin15AnchoredAtom4405 Fin15AnchoredAtom4461 Fin15AnchoredAtom4587 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 11, 12}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 11, 12} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 11, 12}, {4, 6, 7, 11, 12}, {4, 5, 7, 11, 12}, {4, 5, 6, 11, 12}, {4, 5, 6, 7, 12}, {4, 5, 6, 7, 11}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30333 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom4464 chi ∧
      Fin15AnchoredAtom4590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4366 Fin15AnchoredAtom4367 Fin15AnchoredAtom4387
    Fin15AnchoredAtom4408 Fin15AnchoredAtom4464 Fin15AnchoredAtom4590 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 12, 13}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 12, 13} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 13}, {4, 6, 7, 12, 13}, {4, 5, 7, 12, 13}, {4, 5, 6, 12, 13}, {4, 5, 6, 7, 13}, {4, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30334 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom4465 chi ∧
      Fin15AnchoredAtom4591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4366 Fin15AnchoredAtom4368 Fin15AnchoredAtom4388
    Fin15AnchoredAtom4409 Fin15AnchoredAtom4465 Fin15AnchoredAtom4591 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 12, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 12, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 12, 14}, {4, 6, 7, 12, 14}, {4, 5, 7, 12, 14}, {4, 5, 6, 12, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 12}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
  rw [hfam] at hmem
  simp only [Multiset.mem_coe, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact n5
  · exact n4
  · exact n3
  · exact n2
  · exact n1
  · exact n0

theorem fin15Anchored_clause30335 (chi : TripleColoring 15)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :
    ¬(Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom4466 chi ∧
      Fin15AnchoredAtom4592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom4367 Fin15AnchoredAtom4368 Fin15AnchoredAtom4389
    Fin15AnchoredAtom4410 Fin15AnchoredAtom4466 Fin15AnchoredAtom4592 at hbad
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hbad
  apply hnoStrong
  refine ⟨{4, 5, 6, 7, 13, 14}, by simp, by decide, ?_⟩
  refine isStrongPolygonSet_of_forall_five chi _ (by decide) ?_
  intro t hsub hcard
  have hmem : t ∈ (({4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val :=
    Finset.mem_def.mp (Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩)
  have hfam : (({4, 5, 6, 7, 13, 14} : Finset (Fin 15)).powersetCard 5).val =
      (↑([{5, 6, 7, 13, 14}, {4, 6, 7, 13, 14}, {4, 5, 7, 13, 14}, {4, 5, 6, 13, 14}, {4, 5, 6, 7, 14}, {4, 5, 6, 7, 13}] : List (Finset (Fin 15))) :
        Multiset (Finset (Fin 15))) := rfl
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
