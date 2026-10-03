import ESBlueprint.B.ExistsCapStartPeelOfOneChangeNoCapSuccNoCup

namespace ErdosSzekeres

/-- A cup ending where a cap starts can extend one of them under the one-change law; the nearest points adjacent to their common endpoint decide the extension. This is the overlap invariant used to count the L3 first-point layers.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_six_pred_pred_of_seven_le -/
theorem containsCupSet_succ_or_containsCapSet_succ_of_oneChange_common_endpoint {n : ℕ} {χ : TripleColoring n} {P C : Finset (Fin n)} {z : Fin n}
(hone : OneChangeOn χ (P ∪ C)) (hPtwo : 2 ≤ P.card) (hCtwo : 2 ≤ C.card)
(hzP : z ∈ P) (hzC : z ∈ C) (hPcup : IsCupSet χ P) (hCcap : IsCapSet χ C)
(hPmax : ∀ x ∈ P, x ≤ z) (hCmin : ∀ x ∈ C, z ≤ x) :
ContainsCupSet χ (P ∪ C) (P.card + 1) ∨ ContainsCapSet χ (P ∪ C) (C.card + 1) := by
  classical
  have hCrest : (C.erase z).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hzC]
    omega
  let a := (C.erase z).min' hCrest
  have haErase : a ∈ C.erase z := Finset.min'_mem _ _
  have haC : a ∈ C := (Finset.mem_erase.mp haErase).2
  have hza : z < a := by
    have := hCmin a haC
    have := (Finset.mem_erase.mp haErase).1
    omega
  have hCnext : ∀ y ∈ C, z < y → a ≤ y := by
    intro y hy hzy
    exact Finset.min'_le _ y (Finset.mem_erase.mpr ⟨ne_of_gt hzy, hy⟩)
  have haNotP : a ∉ P := by
    intro haP
    have := hPmax a haP
    omega
  have hPrest : (P.erase z).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hzP]
    omega
  let b := (P.erase z).max' hPrest
  have hbErase : b ∈ P.erase z := Finset.max'_mem _ _
  have hbP : b ∈ P := (Finset.mem_erase.mp hbErase).2
  have hbz : b < z := by
    have := hPmax b hbP
    have := (Finset.mem_erase.mp hbErase).1
    omega
  have hPprev : ∀ y ∈ P, y < z → y ≤ b := by
    intro y hy hyz
    exact Finset.le_max' _ y (Finset.mem_erase.mpr ⟨ne_of_lt hyz, hy⟩)
  cases hturn : χ ⟨b, z, a, hbz, hza⟩ with
  | left =>
    have hnewSub : insert a P ⊆ P ∪ C :=
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ haC, Finset.subset_union_left⟩
    have hnewCup : IsCupSet χ (insert a P) :=
      monochromaticSet_insert_max_of_oneChange hbP hzP hbz hza hPmax hPprev
        hPcup (hone.mono hnewSub) hturn
    exact Or.inl ⟨insert a P, hnewSub, Finset.card_insert_of_notMem haNotP, hnewCup⟩
  | right =>
    have hbNotC : b ∉ C := by
      intro hbC
      have := hCmin b hbC
      omega
    have hcapSub : insert b C ⊆ P ∪ C :=
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _ hbP, Finset.subset_union_right⟩
    have hnewCap : IsCapSet χ (insert b C) :=
      monochromaticSet_insert_min_of_oneChange hzC haC hza hbz hCmin hCnext
        hCcap (hone.mono hcapSub) hturn
    exact Or.inr ⟨insert b C, hcapSub, Finset.card_insert_of_notMem hbNotC, hnewCap⟩


end ErdosSzekeres
