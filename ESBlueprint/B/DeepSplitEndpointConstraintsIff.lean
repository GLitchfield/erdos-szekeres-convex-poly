import ErdosSzekeres.Duality

namespace ErdosSzekeres

/-- At any deep-below split, arbitrary cup/cap set predicates hold on the parent exactly when they hold on pure nongrowing-child chains and on growing-child chains augmented by opposite-child sweep endpoints of the entire union. Empty chains and children are retained; this is the exact chain-constraint component of profile gluing.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.HasDeepBelowSplit.upper_mem_cup_isSweepEndpoint, ErdosSzekeres.HasDeepBelowSplit.lower_mem_cap_isSweepEndpoint, ErdosSzekeres.isCupSet_dual_iff
@dangling-ok General endpoint-constraint equivalence required for R24 exact DS compatible-profile gluing; complements accepted strong coupling while joint sub-zone placement, occupancy and closed loss invariant remain open. -/
theorem deepSplit_endpoint_constraints_iff {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)} (hdeep : HasDeepBelowSplit χ lower upper) (cupAllowed capAllowed : Finset (Fin n) → Prop) : ((∀ T : Finset (Fin n), T ⊆ lower ∪ upper → IsCupSet χ T → cupAllowed T) ∧ (∀ T : Finset (Fin n), T ⊆ lower ∪ upper → IsCapSet χ T → capAllowed T)) ↔ ((∀ T : Finset (Fin n), T ⊆ upper → IsCupSet χ T → cupAllowed T) ∧ (∀ T : Finset (Fin n), T ⊆ lower → IsCapSet χ T → capAllowed T) ∧ (∀ C E : Finset (Fin n), C ⊆ lower → E ⊆ upper → IsCupSet χ C → (∀ q ∈ E, HasDeepBelowSplit.IsSweepEndpoint (C ∪ E) q) → cupAllowed (C ∪ E)) ∧ (∀ C E : Finset (Fin n), C ⊆ upper → E ⊆ lower → IsCapSet χ C → (∀ q ∈ E, HasDeepBelowSplit.IsSweepEndpoint (C ∪ E) q) → capAllowed (C ∪ E))) := by
  classical
  have cup_glue (ψ : TripleColoring n) (L U C E : Finset (Fin n))
      (hd : HasDeepBelowSplit ψ L U) (hCL : C ⊆ L) (hEU : E ⊆ U)
      (hC : IsCupSet ψ C)
      (hend : ∀ q ∈ E, HasDeepBelowSplit.IsSweepEndpoint (C ∪ E) q) :
      IsCupSet ψ (C ∪ E) := by
    have hs := hd.mono hCL hEU
    intro t hi hj hk
    have hjC : t.j ∈ C := by
      rcases Finset.mem_union.mp hj with hjC | hjE
      · exact hjC
      · rcases hend t.j hjE with hleft | hright
        · have := hleft t.i hi
          have := t.hij
          omega
        · have := hright t.k hk
          have := t.hjk
          omega
    by_cases hallC : t.i ∈ C ∧ t.j ∈ C ∧ t.k ∈ C
    · exact hC t hallC.1 hallC.2.1 hallC.2.2
    have hnotE : ¬ (t.i ∈ E ∧ t.j ∈ E ∧ t.k ∈ E) := by
      intro h
      exact Finset.disjoint_left.mp hs.disjoint hjC h.2.1
    simpa [hjC] using hs.crossing t hi hj hk hallC hnotE
  have cap_glue (C E : Finset (Fin n)) (hCU : C ⊆ upper)
      (hEL : E ⊆ lower) (hC : IsCapSet χ C)
      (hend : ∀ q ∈ E, HasDeepBelowSplit.IsSweepEndpoint (C ∪ E) q) :
      IsCapSet χ (C ∪ E) :=
    isCupSet_dual_iff.mp (cup_glue χ.dual upper lower C E hdeep.dual
      hCU hEL (isCupSet_dual_iff.mpr hC) hend)
  have partition (T X Y : Finset (Fin n)) (hT : T ⊆ X ∪ Y) :
      (T ∩ X) ∪ (T ∩ Y) = T := by
    ext q
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    · intro hq
      rcases Finset.mem_union.mp (hT hq) with hX | hY
      · exact Or.inl ⟨hq, hX⟩
      · exact Or.inr ⟨hq, hY⟩
  constructor
  · rintro ⟨hCup, hCap⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro T hTU hT
      exact hCup T (hTU.trans Finset.subset_union_right) hT
    · intro T hTL hT
      exact hCap T (hTL.trans Finset.subset_union_left) hT
    · intro C E hCL hEU hC hend
      exact hCup (C ∪ E) (Finset.union_subset_union hCL hEU)
        (cup_glue χ lower upper C E hdeep hCL hEU hC hend)
    · intro C E hCU hEL hC hend
      exact hCap (C ∪ E)
        (by simpa [Finset.union_comm] using Finset.union_subset_union hCU hEL)
        (cap_glue C E hCU hEL hC hend)
  · rintro ⟨hCupU, hCapL, hCupMixed, hCapMixed⟩
    constructor
    · intro T hTS hT
      by_cases hmeet : (T ∩ lower).Nonempty
      · have heq := partition T lower upper hTS
        rw [← heq]
        refine hCupMixed (T ∩ lower) (T ∩ upper)
          Finset.inter_subset_right Finset.inter_subset_right
          (FinsetPolygon.IsCupSet.mono hT Finset.inter_subset_left) ?_
        intro q hq
        rw [heq]
        exact hdeep.upper_mem_cup_isSweepEndpoint hTS hT hmeet
          (Finset.mem_inter.mp hq).1 (Finset.mem_inter.mp hq).2
      · have hTU : T ⊆ upper := by
          intro q hq
          rcases Finset.mem_union.mp (hTS hq) with hL | hU
          · exact False.elim (hmeet ⟨q, Finset.mem_inter.mpr ⟨hq, hL⟩⟩)
          · exact hU
        exact hCupU T hTU hT
    · intro T hTS hT
      by_cases hmeet : (T ∩ upper).Nonempty
      · have heq := partition T upper lower
          (by simpa [Finset.union_comm] using hTS)
        rw [← heq]
        refine hCapMixed (T ∩ upper) (T ∩ lower)
          Finset.inter_subset_right Finset.inter_subset_right
          (FinsetPolygon.IsCapSet.mono hT Finset.inter_subset_left) ?_
        intro q hq
        rw [heq]
        exact hdeep.lower_mem_cap_isSweepEndpoint hTS hT hmeet
          (Finset.mem_inter.mp hq).1 (Finset.mem_inter.mp hq).2
      · have hTL : T ⊆ lower := by
          intro q hq
          rcases Finset.mem_union.mp (hTS hq) with hL | hU
          · exact hL
          · exact False.elim (hmeet ⟨q, Finset.mem_inter.mpr ⟨hq, hU⟩⟩)
        exact hCapL T hTL hT


end ErdosSzekeres
