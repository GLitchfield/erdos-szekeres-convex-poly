module

public import ErdosSzekeres.StructuralChargingNextState578Dual
public import ErdosSzekeres.StructuralChargingNextState578PrivateCaps
import ErdosSzekeres.StructuralChargingNextState578SpanCounterexample

@[expose] public section

/-!
# Cross-color packing in the state-578 color-dual reservoir

The exact 32-vertex swapped singleton-lower gate has four-cup density in every
23-vertex restriction.  Three such cups can be selected disjointly.  After
removing their twelve vertices, the strict `(4,5,8)` predecessor can be spent
three times on residual supports of sizes `20`, `16`, and `12`, producing
three further pairwise-disjoint four-caps.

This file packages that global `3+3` witness supply.  It does not claim that
the six witnesses already force a common decomposition-tree split.
-/

namespace ErdosSzekeres

/-- Three disjoint four-cups and three disjoint four-caps in one support.
The cups are represented as cap witnesses for the dual coloring so that the
existing cap-density packing API applies directly. -/
structure ThreeDisjointCupCapFourPacking578
    {n : ℕ} (χ : TripleColoring n) (support : Finset (Fin n)) where
  cup₁ : Finset (Fin n)
  cup₂ : Finset (Fin n)
  cup₃ : Finset (Fin n)
  cap₁ : Finset (Fin n)
  cap₂ : Finset (Fin n)
  cap₃ : Finset (Fin n)
  cup₁_mem : cup₁ ∈ capWitnesses χ.dual support 4
  cup₂_mem : cup₂ ∈ capWitnesses χ.dual support 4
  cup₃_mem : cup₃ ∈ capWitnesses χ.dual support 4
  cap₁_mem : cap₁ ∈ capWitnesses χ support 4
  cap₂_mem : cap₂ ∈ capWitnesses χ support 4
  cap₃_mem : cap₃ ∈ capWitnesses χ support 4
  cup₁_cup₂ : Disjoint cup₁ cup₂
  cup₁_cup₃ : Disjoint cup₁ cup₃
  cup₂_cup₃ : Disjoint cup₂ cup₃
  cap₁_cap₂ : Disjoint cap₁ cap₂
  cap₁_cap₃ : Disjoint cap₁ cap₃
  cap₂_cap₃ : Disjoint cap₂ cap₃
  colors_disjoint : Disjoint (cup₁ ∪ cup₂ ∪ cup₃) (cap₁ ∪ cap₂ ∪ cap₃)

/-- The four-cup density of the swapped 32-vertex reservoir supplies three
pairwise-disjoint four-cups. -/
theorem exists_three_pairwiseDisjoint_cupFour_of_colorDualLower_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ∃ cup₁ cup₂ cup₃,
      cup₁ ∈ capWitnesses χ.dual reservoir 4 ∧
      cup₂ ∈ capWitnesses χ.dual reservoir 4 ∧
      cup₃ ∈ capWitnesses χ.dual reservoir 4 ∧
      Disjoint cup₁ cup₂ ∧ Disjoint cup₁ cup₃ ∧ Disjoint cup₂ cup₃ := by
  obtain ⟨cup₁, hcup₁Sub, hcup₁Card, hcup₁⟩ :=
    containsCupFour_of_colorDualLower_large_subset_at_578
      hreservoir (by omega) Finset.Subset.rfl hnoCap hnoStrong
  have hcup₁Mem : cup₁ ∈ capWitnesses χ.dual reservoir 4 :=
    mem_capWitnesses.mpr
      ⟨hcup₁Sub, hcup₁Card, isCapSet_dual_iff.mpr hcup₁⟩
  have hdenseDual : ∀ subset : Finset (Fin n), subset ⊆ reservoir →
      subset.card = 23 → ContainsCapSet χ.dual subset 4 := by
    intro subset hsubset hsubsetCard
    apply containsCapSet_dual_iff.mpr
    exact containsCupFour_of_colorDualLower_large_subset_at_578
      (hreservoir.subset hsubset (Finset.card_pos.mp (by omega)))
      (by omega) hsubset hnoCap hnoStrong
  obtain ⟨cup₂, cup₃, hcup₂Mem, hcup₃Mem, hcup₁Cup₂,
      hcup₁Cup₃, hcup₂Cup₃⟩ :=
    exists_two_fourCaps_pairwiseDisjoint_from_given_at_32_23
      hcard hcup₁Mem hdenseDual
  exact ⟨cup₁, cup₂, cup₃, hcup₁Mem, hcup₂Mem, hcup₃Mem,
    hcup₁Cup₂, hcup₁Cup₃, hcup₂Cup₃⟩

/-- The strict `(4,5,8)` predecessor supplies a four-cap in any decomposable
11-vertex subreservoir when the parent has no five-cup or strong eight-set. -/
theorem containsCapFour_of_predecessor_458
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir subset : Finset (Fin n)}
    (hsubset : IsDecomposableOn χ subset) (hcard : 11 ≤ subset.card)
    (hsub : subset ⊆ reservoir)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ContainsCapSet χ subset 4 := by
  have hthreshold : decomposableThreshold 4 5 8 = 10 := by
    norm_num [decomposableThreshold, Nat.choose]
  rcases h458 hsubset (by omega) with hcap | hcup | hstrong
  · exact hcap
  · exact (hnoCup (FinsetPolygon.ContainsCupSet.mono hcup
      (hsub.trans Finset.subset_union_right))).elim
  · exact (hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
      (hsub.trans Finset.subset_union_right))).elim

/-- The density and strict-predecessor inputs combine into a global packing of
three disjoint four-cups and three disjoint four-caps. -/
theorem exists_threeDisjointCupCapFourPacking_of_colorDualLower_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    Nonempty (ThreeDisjointCupCapFourPacking578 χ reservoir) := by
  obtain ⟨cup₁, cup₂, cup₃, hcup₁Mem, hcup₂Mem, hcup₃Mem,
      hcup₁Cup₂, hcup₁Cup₃, hcup₂Cup₃⟩ :=
    exists_three_pairwiseDisjoint_cupFour_of_colorDualLower_at_32
      hreservoir hcard hnoCap hnoStrong
  have hcup₁Data := mem_capWitnesses.mp hcup₁Mem
  have hcup₂Data := mem_capWitnesses.mp hcup₂Mem
  have hcup₃Data := mem_capWitnesses.mp hcup₃Mem
  let cupSupport := cup₁ ∪ cup₂ ∪ cup₃
  have hcupSupportSub : cupSupport ⊆ reservoir := by
    exact Finset.union_subset
      (Finset.union_subset hcup₁Data.1 hcup₂Data.1) hcup₃Data.1
  have hcup₁₂Cup₃ : Disjoint (cup₁ ∪ cup₂) cup₃ := by
    exact Finset.disjoint_union_left.mpr ⟨hcup₁Cup₃, hcup₂Cup₃⟩
  have hcupSupportCard : cupSupport.card = 12 := by
    rw [Finset.card_union_of_disjoint hcup₁₂Cup₃,
      Finset.card_union_of_disjoint hcup₁Cup₂,
      hcup₁Data.2.1, hcup₂Data.2.1, hcup₃Data.2.1]
  let rest₁ := reservoir \ cupSupport
  have hrest₁Card : rest₁.card = 20 := by
    rw [Finset.card_sdiff_of_subset hcupSupportSub, hcard, hcupSupportCard]
  have hrest₁Decomposable : IsDecomposableOn χ rest₁ :=
    hreservoir.subset Finset.sdiff_subset (Finset.card_pos.mp (by omega))
  obtain ⟨cap₁, hcap₁Rest, hcap₁Card, hcap₁⟩ :=
    containsCapFour_of_predecessor_458 h458 hrest₁Decomposable
      (by omega) Finset.sdiff_subset hnoCup hnoStrong
  have hcap₁Support : cap₁ ⊆ reservoir :=
    hcap₁Rest.trans Finset.sdiff_subset
  let rest₂ := rest₁ \ cap₁
  have hrest₂Card : rest₂.card = 16 := by
    rw [Finset.card_sdiff_of_subset hcap₁Rest, hrest₁Card, hcap₁Card]
  have hrest₂Decomposable : IsDecomposableOn χ rest₂ :=
    hrest₁Decomposable.subset Finset.sdiff_subset
      (Finset.card_pos.mp (by omega))
  obtain ⟨cap₂, hcap₂Rest₂, hcap₂Card, hcap₂⟩ :=
    containsCapFour_of_predecessor_458 h458 hrest₂Decomposable
      (by omega) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      hnoCup hnoStrong
  have hcap₂Rest₁ : cap₂ ⊆ rest₁ :=
    hcap₂Rest₂.trans Finset.sdiff_subset
  have hcap₂Support : cap₂ ⊆ reservoir :=
    hcap₂Rest₁.trans Finset.sdiff_subset
  let rest₃ := rest₂ \ cap₂
  have hrest₃Card : rest₃.card = 12 := by
    rw [Finset.card_sdiff_of_subset hcap₂Rest₂, hrest₂Card, hcap₂Card]
  have hrest₃Decomposable : IsDecomposableOn χ rest₃ :=
    hrest₂Decomposable.subset Finset.sdiff_subset
      (Finset.card_pos.mp (by omega))
  obtain ⟨cap₃, hcap₃Rest₃, hcap₃Card, hcap₃⟩ :=
    containsCapFour_of_predecessor_458 h458 hrest₃Decomposable
      (by omega) (Finset.sdiff_subset.trans (Finset.sdiff_subset.trans
        Finset.sdiff_subset)) hnoCup hnoStrong
  have hcap₃Rest₂ : cap₃ ⊆ rest₂ :=
    hcap₃Rest₃.trans Finset.sdiff_subset
  have hcap₃Rest₁ : cap₃ ⊆ rest₁ :=
    hcap₃Rest₂.trans Finset.sdiff_subset
  have hcap₃Support : cap₃ ⊆ reservoir :=
    hcap₃Rest₁.trans Finset.sdiff_subset
  have hcap₁Cap₂ : Disjoint cap₁ cap₂ := by
    rw [Finset.disjoint_left]
    intro x hxCap₁ hxCap₂
    exact (Finset.mem_sdiff.mp (hcap₂Rest₂ hxCap₂)).2 hxCap₁
  have hcap₁Cap₃ : Disjoint cap₁ cap₃ := by
    rw [Finset.disjoint_left]
    intro x hxCap₁ hxCap₃
    exact (Finset.mem_sdiff.mp (hcap₃Rest₂ hxCap₃)).2 hxCap₁
  have hcap₂Cap₃ : Disjoint cap₂ cap₃ := by
    rw [Finset.disjoint_left]
    intro x hxCap₂ hxCap₃
    exact (Finset.mem_sdiff.mp (hcap₃Rest₃ hxCap₃)).2 hxCap₂
  have hcapUnionRest₁ : cap₁ ∪ cap₂ ∪ cap₃ ⊆ rest₁ := by
    exact Finset.union_subset
      (Finset.union_subset hcap₁Rest hcap₂Rest₁) hcap₃Rest₁
  have hcolorsDisjoint :
      Disjoint cupSupport (cap₁ ∪ cap₂ ∪ cap₃) := by
    rw [Finset.disjoint_left]
    intro x hxCup hxCap
    exact (Finset.mem_sdiff.mp (hcapUnionRest₁ hxCap)).2 hxCup
  exact ⟨{
    cup₁ := cup₁
    cup₂ := cup₂
    cup₃ := cup₃
    cap₁ := cap₁
    cap₂ := cap₂
    cap₃ := cap₃
    cup₁_mem := hcup₁Mem
    cup₂_mem := hcup₂Mem
    cup₃_mem := hcup₃Mem
    cap₁_mem := mem_capWitnesses.mpr ⟨hcap₁Support, hcap₁Card, hcap₁⟩
    cap₂_mem := mem_capWitnesses.mpr ⟨hcap₂Support, hcap₂Card, hcap₂⟩
    cap₃_mem := mem_capWitnesses.mpr ⟨hcap₃Support, hcap₃Card, hcap₃⟩
    cup₁_cup₂ := hcup₁Cup₂
    cup₁_cup₃ := hcup₁Cup₃
    cup₂_cup₃ := hcup₂Cup₃
    cap₁_cap₂ := hcap₁Cap₂
    cap₁_cap₃ := hcap₁Cap₃
    cap₂_cap₃ := hcap₂Cap₃
    colors_disjoint := hcolorsDisjoint
  }⟩

/-- The rigid incidence alternative for a four-cap meeting three disjoint
four-cups: its intersection cardinalities are `2,1,1` in some order. -/
def TwoOneOneCupIncidence578
    {n : ℕ} (cap cup₁ cup₂ cup₃ : Finset (Fin n)) : Prop :=
  ((cap ∩ cup₁).card = 2 ∧ (cap ∩ cup₂).card = 1 ∧
      (cap ∩ cup₃).card = 1) ∨
    ((cap ∩ cup₁).card = 1 ∧ (cap ∩ cup₂).card = 2 ∧
      (cap ∩ cup₃).card = 1) ∨
    ((cap ∩ cup₁).card = 1 ∧ (cap ∩ cup₂).card = 1 ∧
      (cap ∩ cup₃).card = 2)

/-- Regenerate an opposite-color witness inside the union of the three cups.
The new cap either misses one selected cup or has the exact `2+1+1`
incidence profile. -/
theorem ThreeDisjointCupCapFourPacking578.exists_regeneratedCap_in_cups
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ∃ regenerated,
      regenerated ∈ capWitnesses χ reservoir 4 ∧
      regenerated ⊆ packing.cup₁ ∪ packing.cup₂ ∪ packing.cup₃ ∧
      ((∃ cup ∈ ({packing.cup₁, packing.cup₂, packing.cup₃} :
          Finset (Finset (Fin n))), Disjoint regenerated cup) ∨
        TwoOneOneCupIncidence578 regenerated
          packing.cup₁ packing.cup₂ packing.cup₃) := by
  have hcup₁Data := mem_capWitnesses.mp packing.cup₁_mem
  have hcup₂Data := mem_capWitnesses.mp packing.cup₂_mem
  have hcup₃Data := mem_capWitnesses.mp packing.cup₃_mem
  let cupSupport := packing.cup₁ ∪ packing.cup₂ ∪ packing.cup₃
  have hcupSupportSub : cupSupport ⊆ reservoir :=
    Finset.union_subset (Finset.union_subset hcup₁Data.1 hcup₂Data.1)
      hcup₃Data.1
  have hcup₁₂Cup₃ : Disjoint (packing.cup₁ ∪ packing.cup₂) packing.cup₃ :=
    Finset.disjoint_union_left.mpr
      ⟨packing.cup₁_cup₃, packing.cup₂_cup₃⟩
  have hcupSupportCard : cupSupport.card = 12 := by
    rw [Finset.card_union_of_disjoint hcup₁₂Cup₃,
      Finset.card_union_of_disjoint packing.cup₁_cup₂,
      hcup₁Data.2.1, hcup₂Data.2.1, hcup₃Data.2.1]
  have hcupSupportDecomposable : IsDecomposableOn χ cupSupport :=
    hreservoir.subset hcupSupportSub (Finset.card_pos.mp (by omega))
  obtain ⟨regenerated, hregeneratedSub, hregeneratedCard, hregeneratedCap⟩ :=
    containsCapFour_of_predecessor_458 h458 hcupSupportDecomposable
      (by omega) hcupSupportSub hnoCup hnoStrong
  have hregeneratedMem : regenerated ∈ capWitnesses χ reservoir 4 :=
    mem_capWitnesses.mpr
      ⟨hregeneratedSub.trans hcupSupportSub,
        hregeneratedCard, hregeneratedCap⟩
  refine ⟨regenerated, hregeneratedMem, hregeneratedSub, ?_⟩
  by_cases hdisjoint₁ : Disjoint regenerated packing.cup₁
  · exact Or.inl ⟨packing.cup₁, by simp, hdisjoint₁⟩
  by_cases hdisjoint₂ : Disjoint regenerated packing.cup₂
  · exact Or.inl ⟨packing.cup₂, by simp, hdisjoint₂⟩
  by_cases hdisjoint₃ : Disjoint regenerated packing.cup₃
  · exact Or.inl ⟨packing.cup₃, by simp, hdisjoint₃⟩
  right
  have hcup₁ : IsCupSet χ packing.cup₁ :=
    isCapSet_dual_iff.mp hcup₁Data.2.2
  have hcup₂ : IsCupSet χ packing.cup₂ :=
    isCapSet_dual_iff.mp hcup₂Data.2.2
  have hcup₃ : IsCupSet χ packing.cup₃ :=
    isCapSet_dual_iff.mp hcup₃Data.2.2
  have hinter₁Le : (regenerated ∩ packing.cup₁).card ≤ 2 :=
    inter_card_le_two_of_cup_cap hcup₁ hregeneratedCap
  have hinter₂Le : (regenerated ∩ packing.cup₂).card ≤ 2 :=
    inter_card_le_two_of_cup_cap hcup₂ hregeneratedCap
  have hinter₃Le : (regenerated ∩ packing.cup₃).card ≤ 2 :=
    inter_card_le_two_of_cup_cap hcup₃ hregeneratedCap
  obtain ⟨x₁, hx₁Regenerated, hx₁Cup⟩ :=
    Finset.not_disjoint_iff.mp hdisjoint₁
  obtain ⟨x₂, hx₂Regenerated, hx₂Cup⟩ :=
    Finset.not_disjoint_iff.mp hdisjoint₂
  obtain ⟨x₃, hx₃Regenerated, hx₃Cup⟩ :=
    Finset.not_disjoint_iff.mp hdisjoint₃
  have hinter₁Pos : 0 < (regenerated ∩ packing.cup₁).card :=
    Finset.card_pos.mpr ⟨x₁, Finset.mem_inter.mpr
      ⟨hx₁Regenerated, hx₁Cup⟩⟩
  have hinter₂Pos : 0 < (regenerated ∩ packing.cup₂).card :=
    Finset.card_pos.mpr ⟨x₂, Finset.mem_inter.mpr
      ⟨hx₂Regenerated, hx₂Cup⟩⟩
  have hinter₃Pos : 0 < (regenerated ∩ packing.cup₃).card :=
    Finset.card_pos.mpr ⟨x₃, Finset.mem_inter.mpr
      ⟨hx₃Regenerated, hx₃Cup⟩⟩
  have hpartition := card_eq_three_inter_of_subset_union
    packing.cup₁_cup₂ packing.cup₁_cup₃ packing.cup₂_cup₃
    hregeneratedSub
  rw [hregeneratedCard] at hpartition
  simp only [TwoOneOneCupIncidence578]
  omega

/-- The exact 32-vertex singleton-root gate reaches the global packing and
regeneration alternative in one theorem.  `hroot` is retained because this is
the downstream interface for the actual gate, although the present extraction
uses only decomposability, cardinality, and target avoidance. -/
theorem exists_dualPackingRegeneration_of_colorDualLower_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (_hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ∃ packing : ThreeDisjointCupCapFourPacking578 χ reservoir,
      ∃ regenerated,
        regenerated ∈ capWitnesses χ reservoir 4 ∧
        regenerated ⊆ packing.cup₁ ∪ packing.cup₂ ∪ packing.cup₃ ∧
        ((∃ cup ∈ ({packing.cup₁, packing.cup₂, packing.cup₃} :
            Finset (Finset (Fin n))), Disjoint regenerated cup) ∨
          TwoOneOneCupIncidence578 regenerated
            packing.cup₁ packing.cup₂ packing.cup₃) := by
  obtain ⟨packing⟩ :=
    exists_threeDisjointCupCapFourPacking_of_colorDualLower_at_32
      h458 hreservoir hcard hnoCap hnoCup hnoStrong
  obtain ⟨regenerated, hmem, hsub, hshape⟩ :=
    packing.exists_regeneratedCap_in_cups
      h458 hreservoir hnoCup hnoStrong
  exact ⟨packing, regenerated, hmem, hsub, hshape⟩

/-- At any one deep split containing the six witnesses, target avoidance
forces a three-vertex defense on one color: either every selected cup crosses
out of the lower child or every selected cap crosses out of the upper child. -/
theorem ThreeDisjointCupCapFourPacking578.commonSplit_defense
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support)
    (node : DecompositionSplit χ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ (node.lower ∪ node.upper) 8) :
    ((¬packing.cup₁ ⊆ node.lower) ∧
      (¬packing.cup₂ ⊆ node.lower) ∧
      (¬packing.cup₃ ⊆ node.lower)) ∨
    ((¬packing.cap₁ ⊆ node.upper) ∧
      (¬packing.cap₂ ⊆ node.upper) ∧
      (¬packing.cap₃ ⊆ node.upper)) := by
  classical
  have clash (cup cap : Finset (Fin n))
      (hcup : cup ∈ capWitnesses χ.dual support 4)
      (hcap : cap ∈ capWitnesses χ support 4)
      (hcupLower : cup ⊆ node.lower) (hcapUpper : cap ⊆ node.upper) : False := by
    have hcupData := mem_capWitnesses.mp hcup
    have hcapData := mem_capWitnesses.mp hcap
    apply hnoStrong
    exact node.deep.containsStrongPolygonSet_of_containsCupCap
      ⟨cup, hcupLower, hcupData.2.1, isCapSet_dual_iff.mp hcupData.2.2⟩
      ⟨cap, hcapUpper, hcapData.2.1, hcapData.2.2⟩ (by omega)
  by_cases hcup₁Lower : packing.cup₁ ⊆ node.lower
  · right
    exact ⟨fun h ↦ clash packing.cup₁ packing.cap₁ packing.cup₁_mem
        packing.cap₁_mem hcup₁Lower h,
      fun h ↦ clash packing.cup₁ packing.cap₂ packing.cup₁_mem
        packing.cap₂_mem hcup₁Lower h,
      fun h ↦ clash packing.cup₁ packing.cap₃ packing.cup₁_mem
        packing.cap₃_mem hcup₁Lower h⟩
  by_cases hcup₂Lower : packing.cup₂ ⊆ node.lower
  · right
    exact ⟨fun h ↦ clash packing.cup₂ packing.cap₁ packing.cup₂_mem
        packing.cap₁_mem hcup₂Lower h,
      fun h ↦ clash packing.cup₂ packing.cap₂ packing.cup₂_mem
        packing.cap₂_mem hcup₂Lower h,
      fun h ↦ clash packing.cup₂ packing.cap₃ packing.cup₂_mem
        packing.cap₃_mem hcup₂Lower h⟩
  by_cases hcup₃Lower : packing.cup₃ ⊆ node.lower
  · right
    exact ⟨fun h ↦ clash packing.cup₃ packing.cap₁ packing.cup₃_mem
        packing.cap₁_mem hcup₃Lower h,
      fun h ↦ clash packing.cup₃ packing.cap₂ packing.cup₃_mem
        packing.cap₂_mem hcup₃Lower h,
      fun h ↦ clash packing.cup₃ packing.cap₃ packing.cup₃_mem
        packing.cap₃_mem hcup₃Lower h⟩
  exact Or.inl ⟨hcup₁Lower, hcup₂Lower, hcup₃Lower⟩

/-- The color-dual endpoint law for a four-cup.  If the cup is not wholly in
the upper child, its two sweep-middle vertices are lower and any upper-child
vertices are sweep endpoints. -/
theorem cupFour_deepSplit_upper_subset_endpoints
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cup : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hcup : cup ∈ capWitnesses χ.dual (lower ∪ upper) 4)
    (hnotUpper : ¬cup ⊆ upper) :
    let c := cup.orderEmbOfFin (mem_capWitnesses.mp hcup).2.1
    c 1 ∈ lower ∧ c 2 ∈ lower ∧ cup ∩ upper ⊆ {c 0, c 3} := by
  have hcup' : cup ∈ capWitnesses χ.dual (upper ∪ lower) 4 := by
    simpa [Finset.union_comm] using hcup
  simpa [Finset.union_comm] using
    capFour_deepSplit_lower_subset_endpoints hsplit.dual hcup' hnotUpper

/-- The endpoint shape exposed when a four-cup is not wholly upper at a deep
split. -/
def CupFourLowerEndpointShape578
    {n : ℕ} (cup lower upper : Finset (Fin n)) : Prop :=
  ∃ hcard : cup.card = 4,
    let c := cup.orderEmbOfFin hcard
    c 1 ∈ lower ∧ c 2 ∈ lower ∧ cup ∩ upper ⊆ {c 0, c 3}

/-- The color-dual endpoint shape exposed when a four-cap is not wholly lower
at a deep split. -/
def CapFourUpperEndpointShape578
    {n : ℕ} (cap lower upper : Finset (Fin n)) : Prop :=
  ∃ hcard : cap.card = 4,
    let c := cap.orderEmbOfFin hcard
    c 1 ∈ upper ∧ c 2 ∈ upper ∧ cap ∩ lower ⊆ {c 0, c 3}

/-- The canonical first decomposition-tree split at which the union of one
four-cup and one disjoint four-cap no longer lies in a single child. -/
structure CupCapFirstJointSplit578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (tree : DecompositionTree χ support)
    (cup cap : Finset (Fin n)) where
  path : List Bool
  node : DecompositionSplit χ
  lookup : tree.splitAtPath path = some node
  allocated : DecompositionTree.IsLowestSeparatingPath (cup ∪ cap) tree path
  union_local : cup ∪ cap ⊆ node.lower ∪ node.upper
  not_all_lower : ¬cup ∪ cap ⊆ node.lower
  not_all_upper : ¬cup ∪ cap ⊆ node.upper

/-- Every disjoint four-cup/four-cap pair in an explicit decomposition tree
has a canonical first joint split. -/
theorem exists_cupCapFirstJointSplit578
    {n : ℕ} {χ : TripleColoring n} {support cup cap : Finset (Fin n)}
    (tree : DecompositionTree χ support)
    (hcup : cup ∈ capWitnesses χ.dual support 4)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hdisjoint : Disjoint cup cap) :
    Nonempty (CupCapFirstJointSplit578 tree cup cap) := by
  have hcupData := mem_capWitnesses.mp hcup
  have hcapData := mem_capWitnesses.mp hcap
  have hunionSub : cup ∪ cap ⊆ support :=
    Finset.union_subset hcupData.1 hcapData.1
  have hunionCard : (cup ∪ cap).card = 8 := by
    rw [Finset.card_union_of_disjoint hdisjoint,
      hcupData.2.1, hcapData.2.1]
  let path := tree.lowestSeparatingPath hunionSub (by omega)
  obtain ⟨node, hlookup, hlocal, hnotLower, hnotUpper⟩ :=
    tree.lowestSeparatingPath_spec hunionSub (by omega)
  exact ⟨{
    path := path
    node := node
    lookup := hlookup
    allocated := tree.lowestSeparatingPath_isLowest hunionSub (by omega)
    union_local := hlocal
    not_all_lower := hnotLower
    not_all_upper := hnotUpper
  }⟩

/-- At a first joint split, a lower-child cup and an upper-child cap would
already form a strong eight-set. -/
theorem CupCapFirstJointSplit578.not_cup_lower_cap_upper_of_noStrongEight
    {n : ℕ} {χ : TripleColoring n} {support cup cap : Finset (Fin n)}
    {tree : DecompositionTree χ support}
    (joint : CupCapFirstJointSplit578 tree cup cap)
    (hcup : cup ∈ capWitnesses χ.dual support 4)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hnoStrong : ¬ContainsStrongPolygonSet χ support 8) :
    ¬(cup ⊆ joint.node.lower ∧ cap ⊆ joint.node.upper) := by
  rintro ⟨hcupLower, hcapUpper⟩
  have hcupData := mem_capWitnesses.mp hcup
  have hcapData := mem_capWitnesses.mp hcap
  have hstrongNode := joint.node.deep.containsStrongPolygonSet_of_containsCupCap
    (u := 4) (a := 4) (k := 8)
    ⟨cup, hcupLower, hcupData.2.1, isCapSet_dual_iff.mp hcupData.2.2⟩
    ⟨cap, hcapUpper, hcapData.2.1, hcapData.2.2⟩ (by omega)
  exact hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrongNode
    (tree.splitAtPath_support_subset joint.lookup))

/-- The exact first-joint-split trichotomy.  Either the cup is not wholly in
the upper child, the cap is not wholly in the lower child, or the pair is
separated in the unfavorable cap-lower/cup-upper orientation. -/
theorem CupCapFirstJointSplit578.cup_crosses_or_cap_crosses_or_reverseSeparated
    {n : ℕ} {χ : TripleColoring n} {support cup cap : Finset (Fin n)}
    {tree : DecompositionTree χ support}
    (joint : CupCapFirstJointSplit578 tree cup cap) :
    ¬cup ⊆ joint.node.upper ∨ ¬cap ⊆ joint.node.lower ∨
      (cup ⊆ joint.node.upper ∧ cap ⊆ joint.node.lower) := by
  by_cases hcupUpper : cup ⊆ joint.node.upper
  · by_cases hcapLower : cap ⊆ joint.node.lower
    · exact Or.inr (Or.inr ⟨hcupUpper, hcapLower⟩)
    · exact Or.inr (Or.inl hcapLower)
  · exact Or.inl hcupUpper

/-- Enrich the set-theoretic trichotomy with the exact four-point endpoint
shapes.  This is the first local consumer of a joint cup/cap address. -/
theorem CupCapFirstJointSplit578.endpointShapes_or_reverseSeparated
    {n : ℕ} {χ : TripleColoring n} {support cup cap : Finset (Fin n)}
    {tree : DecompositionTree χ support}
    (joint : CupCapFirstJointSplit578 tree cup cap)
    (hcup : cup ∈ capWitnesses χ.dual support 4)
    (hcap : cap ∈ capWitnesses χ support 4) :
    (¬cup ⊆ joint.node.upper ∧
      CupFourLowerEndpointShape578 cup joint.node.lower joint.node.upper) ∨
    (¬cap ⊆ joint.node.lower ∧
      CapFourUpperEndpointShape578 cap joint.node.lower joint.node.upper) ∨
    (cup ⊆ joint.node.upper ∧ cap ⊆ joint.node.lower) := by
  have hcupData := mem_capWitnesses.mp hcup
  have hcapData := mem_capWitnesses.mp hcap
  have hcupNode :
      cup ∈ capWitnesses χ.dual (joint.node.lower ∪ joint.node.upper) 4 :=
    mem_capWitnesses.mpr ⟨fun x hx ↦ joint.union_local
      (Finset.mem_union_left cap hx), hcupData.2⟩
  have hcapNode :
      cap ∈ capWitnesses χ (joint.node.lower ∪ joint.node.upper) 4 :=
    mem_capWitnesses.mpr ⟨fun x hx ↦ joint.union_local
      (Finset.mem_union_right cup hx), hcapData.2⟩
  rcases joint.cup_crosses_or_cap_crosses_or_reverseSeparated with
      hcupNotUpper | hcapNotLower | hreverse
  · left
    refine ⟨hcupNotUpper, ⟨hcupData.2.1, ?_⟩⟩
    exact cupFour_deepSplit_upper_subset_endpoints
      joint.node.deep hcupNode hcupNotUpper
  · right
    left
    refine ⟨hcapNotLower, ⟨hcapData.2.1, ?_⟩⟩
    exact capFour_deepSplit_lower_subset_endpoints
      joint.node.deep hcapNode hcapNotLower
  · exact Or.inr (Or.inr hreverse)

end ErdosSzekeres

end
