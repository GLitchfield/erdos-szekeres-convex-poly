import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- Exact deletion criterion at a matched deep-below root: when lower cups have size at most u and upper caps at most a, deleting a set eliminates strong(u+a)-sets exactly when it eliminates them in each child and drops either the lower cup rank or upper cap rank. Crossing polygons form the Cartesian product of maximum chains; children may interleave.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.HasDeepBelowSplit.isStrongPolygonSet_iff_inter_cup_cap, ErdosSzekeres.HasDeepBelowSplit.containsStrongPolygonSet_of_cup_cap
@dangling-ok Approved R20 reusable a5 decomposition-tree hitting invariant suggested by the read a5b notes. This certifies the maximum-chain product obstruction, without asserting a tight cut exists. -/
theorem deepBelow_noStrong_after_delete_iff_child_and_rankDrop {n u a : ℕ} {χ : TripleColoring n} {lower upper removed : Finset (Fin n)}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hnoCup : ¬ContainsCupSet χ lower (u + 1))
    (hnoCap : ¬ContainsCapSet χ upper (a + 1)) :
    (¬ContainsStrongPolygonSet χ ((lower ∪ upper) \ removed) (u + a)) ↔
      (¬ContainsStrongPolygonSet χ (lower \ removed) (u + a)) ∧
      (¬ContainsStrongPolygonSet χ (upper \ removed) (u + a)) ∧
      ((¬ContainsCupSet χ (lower \ removed) u) ∨
        (¬ContainsCapSet χ (upper \ removed) a)) := by
  classical
  let L := lower \ removed
  let U := upper \ removed
  rw [Finset.union_sdiff_distrib]
  change (¬ContainsStrongPolygonSet χ (L ∪ U) (u + a)) ↔
    (¬ContainsStrongPolygonSet χ L (u + a)) ∧
    (¬ContainsStrongPolygonSet χ U (u + a)) ∧
    ((¬ContainsCupSet χ L u) ∨ (¬ContainsCapSet χ U a))
  have hLsub : L ⊆ lower := Finset.sdiff_subset
  have hUsub : U ⊆ upper := Finset.sdiff_subset
  have hd : HasDeepBelowSplit χ L U := hdeep.mono hLsub hUsub
  have cupBound {C : Finset (Fin n)} (hCsub : C ⊆ L)
      (hCcup : IsCupSet χ C) : C.card ≤ u := by
    by_contra hbig
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
      (by omega : u + 1 ≤ C.card)
    exact hnoCup ⟨T, hTsub.trans (hCsub.trans hLsub), hTcard,
      FinsetPolygon.IsCupSet.mono hCcup hTsub⟩
  have capBound {C : Finset (Fin n)} (hCsub : C ⊆ U)
      (hCcap : IsCapSet χ C) : C.card ≤ a := by
    by_contra hbig
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
      (by omega : a + 1 ≤ C.card)
    exact hnoCap ⟨T, hTsub.trans (hCsub.trans hUsub), hTcard,
      FinsetPolygon.IsCapSet.mono hCcap hTsub⟩
  constructor
  · intro hno
    refine ⟨?_, ?_, ?_⟩
    · intro hstrong
      exact hno (FinsetPolygon.ContainsStrongPolygonSet.mono
        hstrong Finset.subset_union_left)
    · intro hstrong
      exact hno (FinsetPolygon.ContainsStrongPolygonSet.mono
        hstrong Finset.subset_union_right)
    · by_cases hcup : ContainsCupSet χ L u
      · right
        intro ⟨cap, hcapSub, hcapCard, hcap⟩
        obtain ⟨cup, hcupSub, hcupCard, hcup⟩ := hcup
        exact hno (hd.containsStrongPolygonSet_of_cup_cap
          hcupSub hcapSub hcup hcap (by rw [hcupCard, hcapCard]))
      · exact Or.inl hcup
  · rintro ⟨hnoL, hnoU, hdrop⟩ ⟨P, hPsub, hPcard, hPstrong⟩
    by_cases hPL : (P ∩ L).Nonempty
    · by_cases hPU : (P ∩ U).Nonempty
      · obtain ⟨hcup, hcap⟩ :=
          (hd.isStrongPolygonSet_iff_inter_cup_cap hPsub hPL hPU).mp hPstrong
        have hcupBound := cupBound Finset.inter_subset_right hcup
        have hcapBound := capBound Finset.inter_subset_right hcap
        have hpartition : (P ∩ L) ∪ (P ∩ U) = P := by
          apply Finset.Subset.antisymm
            (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
          intro x hx
          rcases Finset.mem_union.mp (hPsub hx) with hxL | hxU
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxL⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxU⟩)
        have hsum : (P ∩ L).card + (P ∩ U).card = u + a := by
          rw [← Finset.card_union_of_disjoint
            (hd.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right),
            hpartition, hPcard]
        have hcupCard : (P ∩ L).card = u := by omega
        have hcapCard : (P ∩ U).card = a := by omega
        rcases hdrop with hdrop | hdrop
        · exact hdrop ⟨P ∩ L, Finset.inter_subset_right, hcupCard, hcup⟩
        · exact hdrop ⟨P ∩ U, Finset.inter_subset_right, hcapCard, hcap⟩
      · apply hnoL ⟨P, ?_, hPcard, hPstrong⟩
        intro x hx
        rcases Finset.mem_union.mp (hPsub hx) with hxL | hxU
        · exact hxL
        · exact (hPU ⟨x, Finset.mem_inter.mpr ⟨hx, hxU⟩⟩).elim
    · apply hnoU ⟨P, ?_, hPcard, hPstrong⟩
      intro x hx
      rcases Finset.mem_union.mp (hPsub hx) with hxL | hxU
      · exact (hPL ⟨x, Finset.mem_inter.mpr ⟨hx, hxL⟩⟩).elim
      · exact hxU


end ErdosSzekeres
