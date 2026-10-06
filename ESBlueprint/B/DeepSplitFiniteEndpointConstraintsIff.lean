import ESBlueprint.B.DeepSplitTwoEndpointExtensions

namespace ErdosSzekeres

/-- For any deep split and arbitrary cup/cap predicates, all parent chain constraints are equivalent to pure child chains and explicit one or two exterior opposite-child endpoint insertions, including empty chains and children.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.deepSplit_two_endpoint_extensions, ErdosSzekeres.HasDeepBelowSplit.cup_inter_upper_card_le_two, ErdosSzekeres.HasDeepBelowSplit.upper_mem_cup_isSweepEndpoint
@dangling-ok General R24 Q3 finite gain criterion underlying endpoint matrix refinement; no extrema optimization, closed N formula or context-bound equivalence is asserted. -/
theorem deepSplit_finite_endpoint_constraints_iff {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)} (hdeep : HasDeepBelowSplit χ lower upper) (cupAllowed capAllowed : Finset (Fin n) → Prop) : ((∀ T : Finset (Fin n), T ⊆ lower ∪ upper → IsCupSet χ T → cupAllowed T) ∧ (∀ T : Finset (Fin n), T ⊆ lower ∪ upper → IsCapSet χ T → capAllowed T)) ↔ (((∀ T : Finset (Fin n), T ⊆ lower → IsCupSet χ T → cupAllowed T) ∧ (∀ T : Finset (Fin n), T ⊆ upper → IsCupSet χ T → cupAllowed T) ∧ (∀ C : Finset (Fin n), C ⊆ lower → IsCupSet χ C → ∀ q : Fin n, q ∈ upper → HasDeepBelowSplit.IsSweepEndpoint C q → cupAllowed (insert q C)) ∧ (∀ C : Finset (Fin n), C ⊆ lower → IsCupSet χ C → ∀ x y : Fin n, x ∈ upper → y ∈ upper → x < y → (∀ z ∈ C, x < z) → (∀ z ∈ C, z < y) → cupAllowed (insert x (insert y C)))) ∧ ((∀ T : Finset (Fin n), T ⊆ upper → IsCapSet χ T → capAllowed T) ∧ (∀ T : Finset (Fin n), T ⊆ lower → IsCapSet χ T → capAllowed T) ∧ (∀ C : Finset (Fin n), C ⊆ upper → IsCapSet χ C → ∀ q : Fin n, q ∈ lower → HasDeepBelowSplit.IsSweepEndpoint C q → capAllowed (insert q C)) ∧ (∀ C : Finset (Fin n), C ⊆ upper → IsCapSet χ C → ∀ x y : Fin n, x ∈ lower → y ∈ lower → x < y → (∀ z ∈ C, x < z) → (∀ z ∈ C, z < y) → capAllowed (insert x (insert y C))))) := by
  classical
  have cup_iff (ψ : TripleColoring n) (L U : Finset (Fin n))
      (hd : HasDeepBelowSplit ψ L U) (allowed : Finset (Fin n) → Prop) :
      (∀ T : Finset (Fin n), T ⊆ L ∪ U → IsCupSet ψ T → allowed T) ↔
      ((∀ T : Finset (Fin n), T ⊆ L → IsCupSet ψ T → allowed T) ∧
       (∀ T : Finset (Fin n), T ⊆ U → IsCupSet ψ T → allowed T) ∧
       (∀ C : Finset (Fin n), C ⊆ L → IsCupSet ψ C → ∀ q : Fin n,
         q ∈ U → HasDeepBelowSplit.IsSweepEndpoint C q → allowed (insert q C)) ∧
       (∀ C : Finset (Fin n), C ⊆ L → IsCupSet ψ C → ∀ x y : Fin n,
         x ∈ U → y ∈ U → x < y → (∀ z ∈ C, x < z) →
         (∀ z ∈ C, z < y) → allowed (insert x (insert y C)))) := by
    constructor
    · intro hall
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro T hTL hT
        exact hall T (hTL.trans Finset.subset_union_left) hT
      · intro T hTU hT
        exact hall T (hTU.trans Finset.subset_union_right) hT
      · intro C hCL hC q hqU hend
        have hsub : insert q C ⊆ L ∪ U :=
          Finset.insert_subset_iff.mpr
            ⟨Finset.mem_union_right _ hqU, hCL.trans Finset.subset_union_left⟩
        apply hall _ hsub
        rcases hend with hleft | hright
        · exact hd.insert_upper_isCupSet_of_isLeftSweepEndpoint hCL hC hqU hleft
        · exact hd.insert_upper_isCupSet_of_isRightSweepEndpoint hCL hC hqU hright
      · intro C hCL hC x y hxU hyU hxy hleft hright
        have hsub : insert x (insert y C) ⊆ L ∪ U :=
          Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hxU,
            Finset.insert_subset_iff.mpr
              ⟨Finset.mem_union_right _ hyU, hCL.trans Finset.subset_union_left⟩⟩
        exact hall _ hsub
          ((deepSplit_two_endpoint_extensions hd).1 C hCL hC x y hxU hyU hxy hleft hright)
    · rintro ⟨hL, hU, hOne, hTwo⟩ T hTS hT
      by_cases hmeet : (T ∩ L).Nonempty
      · let C := T ∩ L
        let E := T ∩ U
        have hCL : C ⊆ L := Finset.inter_subset_right
        have hCT : C ⊆ T := Finset.inter_subset_left
        have hEU : E ⊆ U := Finset.inter_subset_right
        have hET : E ⊆ T := Finset.inter_subset_left
        have hC : IsCupSet ψ C := FinsetPolygon.IsCupSet.mono hT hCT
        have hCE : C ∪ E = T := by
          ext z
          simp only [C, E, Finset.mem_union, Finset.mem_inter]
          have hz := hTS (a := z)
          simp only [Finset.mem_union] at hz
          tauto
        have hEcard : E.card ≤ 2 := hd.cup_inter_upper_card_le_two hTS hT hmeet
        by_cases hEempty : E = ∅
        · rw [← hCE, hEempty, Finset.union_empty]
          exact hL C hCL hC
        by_cases hEone : E.card = 1
        · obtain ⟨q, hEq⟩ := Finset.card_eq_one.mp hEone
          have hqE : q ∈ E := by rw [hEq]; simp
          have hqU := hEU hqE
          have hend := hd.upper_mem_cup_isSweepEndpoint hTS hT hmeet (hET hqE) hqU
          have hendC : HasDeepBelowSplit.IsSweepEndpoint C q := by
            rcases hend with hleft | hright
            · exact Or.inl (fun z hz ↦ hleft z (hCT hz))
            · exact Or.inr (fun z hz ↦ hright z (hCT hz))
          have hset : insert q C = T := by
            rw [← hCE, hEq]
            ext z
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
            tauto
          exact hset ▸ hOne C hCL hC q hqU hendC
        have hEpos : 0 < E.card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEempty)
        have hEtwo : E.card = 2 := by omega
        obtain ⟨x, y, hne, hEq⟩ := Finset.card_eq_two.mp hEtwo
        have pairCase (x y : Fin n) (hxy : x < y) (hEq : E = {x, y}) : allowed T := by
          have hxE : x ∈ E := by rw [hEq]; simp
          have hyE : y ∈ E := by rw [hEq]; simp
          have hxU := hEU hxE
          have hyU := hEU hyE
          have hxT := hET hxE
          have hyT := hET hyE
          have hxEnd := hd.upper_mem_cup_isSweepEndpoint hTS hT hmeet hxT hxU
          have hyEnd := hd.upper_mem_cup_isSweepEndpoint hTS hT hmeet hyT hyU
          have hleft : ∀ z ∈ C, x < z := by
            intro z hz
            have hneq : z ≠ x := by
              intro heq
              subst z
              exact Finset.disjoint_left.mp hd.disjoint (hCL hz) hxU
            rcases hxEnd with hmin | hmax
            · have hle := hmin z (hCT hz)
              omega
            · have hle := hmax y hyT
              omega
          have hright : ∀ z ∈ C, z < y := by
            intro z hz
            have hneq : z ≠ y := by
              intro heq
              subst z
              exact Finset.disjoint_left.mp hd.disjoint (hCL hz) hyU
            rcases hyEnd with hmin | hmax
            · have hle := hmin x hxT
              omega
            · have hle := hmax z (hCT hz)
              omega
          have hset : insert x (insert y C) = T := by
            rw [← hCE, hEq]
            ext z
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
            tauto
          exact hset ▸ hTwo C hCL hC x y hxU hyU hxy hleft hright
        rcases lt_or_gt_of_ne hne with hxy | hyx
        · exact pairCase x y hxy hEq
        · exact pairCase y x hyx (by simpa [Finset.pair_comm] using hEq)
      · have hTU : T ⊆ U := by
          intro q hq
          rcases Finset.mem_union.mp (hTS hq) with hqL | hqU
          · exact False.elim (hmeet ⟨q, Finset.mem_inter.mpr ⟨hq, hqL⟩⟩)
          · exact hqU
        exact hU T hTU hT
  have cap_iff :
      (∀ T : Finset (Fin n), T ⊆ lower ∪ upper → IsCapSet χ T → capAllowed T) ↔
      ((∀ T : Finset (Fin n), T ⊆ upper → IsCapSet χ T → capAllowed T) ∧
       (∀ T : Finset (Fin n), T ⊆ lower → IsCapSet χ T → capAllowed T) ∧
       (∀ C : Finset (Fin n), C ⊆ upper → IsCapSet χ C → ∀ q : Fin n,
         q ∈ lower → HasDeepBelowSplit.IsSweepEndpoint C q → capAllowed (insert q C)) ∧
       (∀ C : Finset (Fin n), C ⊆ upper → IsCapSet χ C → ∀ x y : Fin n,
         x ∈ lower → y ∈ lower → x < y → (∀ z ∈ C, x < z) →
         (∀ z ∈ C, z < y) → capAllowed (insert x (insert y C)))) := by
    simpa only [isCupSet_dual_iff, Finset.union_comm] using
      cup_iff χ.dual upper lower hdeep.dual capAllowed
  exact and_congr (cup_iff χ lower upper hdeep cupAllowed) cap_iff


end ErdosSzekeres
