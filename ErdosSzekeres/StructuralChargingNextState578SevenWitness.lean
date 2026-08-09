module

public import ErdosSzekeres.StructuralChargingNextState578Regeneration

@[expose] public section

/-!
# Saturating the state-578 seven-witness gate

The live regeneration gate already contains four pairwise-disjoint four-caps:
the regenerated cap and the three external caps.  The strict `(4,5,8)`
predecessor can be spent twice more on the residual supports of cardinalities
`16` and `12`.  This file packages the resulting six-cap saturation and its
exact eight-vertex remainder.
-/

namespace ErdosSzekeres

/-- The sixteen vertices occupied by the regenerated cap and the three
external caps. -/
def SevenWitnessRegenerationPacking578.fourCapSupport
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ support) :
    Finset (Fin n) :=
  state.regenerated ∪ state.packing.capSupport

theorem SevenWitnessRegenerationPacking578.fourCapSupport_subset
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ support) :
    state.fourCapSupport ⊆ support := by
  exact Finset.union_subset
    (mem_capWitnesses.mp state.regenerated_mem).1
    (Finset.union_subset
      (Finset.union_subset
        (mem_capWitnesses.mp state.packing.cap₁_mem).1
        (mem_capWitnesses.mp state.packing.cap₂_mem).1)
      (mem_capWitnesses.mp state.packing.cap₃_mem).1)

theorem SevenWitnessRegenerationPacking578.fourCapSupport_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ support) :
    state.fourCapSupport.card = 16 := by
  rw [SevenWitnessRegenerationPacking578.fourCapSupport,
    Finset.card_union_of_disjoint state.regenerated_capSupport,
    (mem_capWitnesses.mp state.regenerated_mem).2.1,
    state.packing.capSupport_card]

/-- A vertex which is a sweep-middle vertex of both a local four-cup and a
local four-cap cannot witness both asymmetric crossing profiles at one deep
split.  Consequently the cup is wholly upper or the cap is wholly lower.

This is the reusable shared-role conflict needed by any global consumer of
the seven-witness gate. -/
theorem cupFour_upper_or_capFour_lower_of_shared_nonendpoint
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cup cap : Finset (Fin n)} {q : Fin n}
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hcup : cup ∈ capWitnesses χ.dual (lower ∪ upper) 4)
    (hcap : cap ∈ capWitnesses χ (lower ∪ upper) 4)
    (hqCup : q ∈ cup) (hqCap : q ∈ cap)
    (hqCupMiddle : ¬HasDeepBelowSplit.IsSweepEndpoint cup q)
    (hqCapMiddle : ¬HasDeepBelowSplit.IsSweepEndpoint cap q) :
    cup ⊆ upper ∨ cap ⊆ lower := by
  by_cases hcupUpper : cup ⊆ upper
  · exact Or.inl hcupUpper
  right
  by_contra hcapLower
  have hcupData := mem_capWitnesses.mp hcup
  have hcapData := mem_capWitnesses.mp hcap
  have hcupLower : (cup ∩ lower).Nonempty := by
    obtain ⟨x, hxCup, hxNotUpper⟩ := Finset.not_subset.mp hcupUpper
    have hxNode := hcupData.1 hxCup
    exact ⟨x, Finset.mem_inter.mpr ⟨hxCup,
      (Finset.mem_union.mp hxNode).resolve_right hxNotUpper⟩⟩
  have hcapUpper : (cap ∩ upper).Nonempty := by
    obtain ⟨x, hxCap, hxNotLower⟩ := Finset.not_subset.mp hcapLower
    have hxNode := hcapData.1 hxCap
    exact ⟨x, Finset.mem_inter.mpr ⟨hxCap,
      (Finset.mem_union.mp hxNode).resolve_left hxNotLower⟩⟩
  have hqNotUpper : q ∉ upper := by
    intro hqUpper
    exact hqCupMiddle (hsplit.upper_mem_cup_isSweepEndpoint
      hcupData.1 (isCapSet_dual_iff.mp hcupData.2.2) hcupLower
      hqCup hqUpper)
  have hqLower : q ∈ lower :=
    (Finset.mem_union.mp (hcupData.1 hqCup)).resolve_right hqNotUpper
  have hqNotLower : q ∉ lower := by
    intro hqLower'
    exact hqCapMiddle (hsplit.lower_mem_cap_isSweepEndpoint
      hcapData.1 hcapData.2.2 hcapUpper hqCap hqLower')
  exact hqNotLower hqLower

/-- The finite four-way state attached to every shared vertex of a local
four-cup/four-cap pair: one witness is wholly in its safe child, or the shared
vertex consumes an endpoint role for at least one witness. -/
def CupCapSharedVertexRole578
    {n : ℕ} (cup cap lower upper : Finset (Fin n)) (q : Fin n) : Prop :=
  cup ⊆ upper ∨ cap ⊆ lower ∨
    HasDeepBelowSplit.IsSweepEndpoint cup q ∨
    HasDeepBelowSplit.IsSweepEndpoint cap q

/-- The complete shared-vertex role ledger for one local cup/cap pair. -/
def CupCapSharedRoleProfile578
    {n : ℕ} (cup cap lower upper : Finset (Fin n)) : Prop :=
  ∀ q ∈ cup ∩ cap, CupCapSharedVertexRole578 cup cap lower upper q

/-- Every local four-cup/four-cap pair has the finite shared-role profile at a
deep split. -/
theorem cupCapSharedRoleProfile578_of_local
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cup cap : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hcup : cup ∈ capWitnesses χ.dual (lower ∪ upper) 4)
    (hcap : cap ∈ capWitnesses χ (lower ∪ upper) 4) :
    CupCapSharedRoleProfile578 cup cap lower upper := by
  intro q hq
  have hqCup := (Finset.mem_inter.mp hq).1
  have hqCap := (Finset.mem_inter.mp hq).2
  simp only [CupCapSharedVertexRole578]
  by_cases hqCupEndpoint : HasDeepBelowSplit.IsSweepEndpoint cup q
  · exact Or.inr (Or.inr (Or.inl hqCupEndpoint))
  by_cases hqCapEndpoint : HasDeepBelowSplit.IsSweepEndpoint cap q
  · exact Or.inr (Or.inr (Or.inr hqCapEndpoint))
  rcases cupFour_upper_or_capFour_lower_of_shared_nonendpoint
      hsplit hcup hcap hqCup hqCap hqCupEndpoint hqCapEndpoint with
    hcupUpper | hcapLower
  · exact Or.inl hcupUpper
  · exact Or.inr (Or.inl hcapLower)

/-- A local four-cap which is not wholly lower has a nonempty upper part, so
the asymmetric endpoint law bounds its lower part by two vertices. -/
theorem capFour_inter_lower_card_le_two_of_not_subset_lower
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cap : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hcap : cap ∈ capWitnesses χ (lower ∪ upper) 4)
    (hnotLower : ¬cap ⊆ lower) :
    (cap ∩ lower).card ≤ 2 := by
  have hcapData := mem_capWitnesses.mp hcap
  have hcapUpper : (cap ∩ upper).Nonempty := by
    obtain ⟨x, hxCap, hxNotLower⟩ := Finset.not_subset.mp hnotLower
    exact ⟨x, Finset.mem_inter.mpr ⟨hxCap,
      (Finset.mem_union.mp (hcapData.1 hxCap)).resolve_left hxNotLower⟩⟩
  exact hsplit.cap_inter_lower_card_le_two
    hcapData.1 hcapData.2.2 hcapUpper

/-- The seven-witness state saturated by two further residual four-caps.
Together with the four caps already in `state`, these are six pairwise-
disjoint four-caps. -/
structure SixCapSaturation578
    {n : ℕ} (χ : TripleColoring n) (support : Finset (Fin n)) where
  state : SevenWitnessRegenerationPacking578 χ support
  cap₅ : Finset (Fin n)
  cap₆ : Finset (Fin n)
  cap₅_mem : cap₅ ∈ capWitnesses χ support 4
  cap₆_mem : cap₆ ∈ capWitnesses χ support 4
  cap₅_fourCapSupport : Disjoint cap₅ state.fourCapSupport
  cap₆_fourCapSupport : Disjoint cap₆ state.fourCapSupport
  cap₅_cap₆ : Disjoint cap₅ cap₆

/-- The six saturated four-caps are pairwise disjoint, in an interface ready
for downstream finite-family arguments. -/
theorem SixCapSaturation578.sixCaps_pairwise
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support) :
    ([saturation.state.regenerated,
      saturation.state.packing.cap₁,
      saturation.state.packing.cap₂,
      saturation.state.packing.cap₃,
      saturation.cap₅,
      saturation.cap₆] : List (Finset (Fin n))).Pairwise Disjoint := by
  have hreg :
      Disjoint saturation.state.regenerated saturation.state.packing.cap₁ ∧
      Disjoint saturation.state.regenerated saturation.state.packing.cap₂ ∧
      Disjoint saturation.state.regenerated saturation.state.packing.cap₃ := by
    simpa [ThreeDisjointCupCapFourPacking578.capSupport] using
      saturation.state.regenerated_capSupport
  have hregSub :
      saturation.state.regenerated ⊆ saturation.state.fourCapSupport :=
    Finset.subset_union_left
  have hcap₁Sub : saturation.state.packing.cap₁ ⊆
      saturation.state.fourCapSupport := by
    intro x hx
    exact Finset.mem_union_right _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have hcap₂Sub : saturation.state.packing.cap₂ ⊆
      saturation.state.fourCapSupport := by
    intro x hx
    exact Finset.mem_union_right _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
  have hcap₃Sub : saturation.state.packing.cap₃ ⊆
      saturation.state.fourCapSupport := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_union_right _ hx)
  have hcap₅ (cap : Finset (Fin n))
      (hsub : cap ⊆ saturation.state.fourCapSupport) :
      Disjoint cap saturation.cap₅ :=
    saturation.cap₅_fourCapSupport.symm.mono hsub Finset.Subset.rfl
  have hcap₆ (cap : Finset (Fin n))
      (hsub : cap ⊆ saturation.state.fourCapSupport) :
      Disjoint cap saturation.cap₆ :=
    saturation.cap₆_fourCapSupport.symm.mono hsub Finset.Subset.rfl
  simpa using ⟨
    ⟨hreg.1, hreg.2.1, hreg.2.2,
      hcap₅ _ hregSub, hcap₆ _ hregSub⟩,
    ⟨
      ⟨saturation.state.packing.cap₁_cap₂,
        saturation.state.packing.cap₁_cap₃,
        hcap₅ _ hcap₁Sub, hcap₆ _ hcap₁Sub⟩,
      ⟨
        ⟨saturation.state.packing.cap₂_cap₃,
          hcap₅ _ hcap₂Sub, hcap₆ _ hcap₂Sub⟩,
        ⟨⟨hcap₅ _ hcap₃Sub, hcap₆ _ hcap₃Sub⟩,
          saturation.cap₅_cap₆⟩⟩⟩⟩

/-- The union of the six disjoint four-caps in a saturated state. -/
def SixCapSaturation578.capSupport
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support) : Finset (Fin n) :=
  saturation.state.fourCapSupport ∪ saturation.cap₅ ∪ saturation.cap₆

theorem SixCapSaturation578.capSupport_subset
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support) :
    saturation.capSupport ⊆ support := by
  exact Finset.union_subset
    (Finset.union_subset saturation.state.fourCapSupport_subset
      (mem_capWitnesses.mp saturation.cap₅_mem).1)
    (mem_capWitnesses.mp saturation.cap₆_mem).1

theorem SixCapSaturation578.capSupport_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support) :
    saturation.capSupport.card = 24 := by
  have hfirst : Disjoint saturation.state.fourCapSupport saturation.cap₅ :=
    saturation.cap₅_fourCapSupport.symm
  have hlast :
      Disjoint (saturation.state.fourCapSupport ∪ saturation.cap₅)
        saturation.cap₆ :=
    Finset.disjoint_union_left.mpr
      ⟨saturation.cap₆_fourCapSupport.symm, saturation.cap₅_cap₆⟩
  rw [SixCapSaturation578.capSupport,
    Finset.card_union_of_disjoint hlast,
    Finset.card_union_of_disjoint hfirst,
    saturation.state.fourCapSupport_card,
    (mem_capWitnesses.mp saturation.cap₅_mem).2.1,
    (mem_capWitnesses.mp saturation.cap₆_mem).2.1]

/-- At any deep split containing the saturated support, if none of the six
caps is wholly lower, their total lower-child demand is at most twelve.  This
is the exact six-cap version of the local two-port bound; it deliberately
makes no unsupported common-address or weak-ordering claim. -/
theorem SixCapSaturation578.sum_cap_inter_lower_card_le_twelve
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (node : DecompositionSplit χ)
    (hlocal : saturation.capSupport ⊆ node.lower ∪ node.upper)
    (hregenerated : ¬saturation.state.regenerated ⊆ node.lower)
    (hcap₁ : ¬saturation.state.packing.cap₁ ⊆ node.lower)
    (hcap₂ : ¬saturation.state.packing.cap₂ ⊆ node.lower)
    (hcap₃ : ¬saturation.state.packing.cap₃ ⊆ node.lower)
    (hcap₅ : ¬saturation.cap₅ ⊆ node.lower)
    (hcap₆ : ¬saturation.cap₆ ⊆ node.lower) :
    (saturation.state.regenerated ∩ node.lower).card +
      (saturation.state.packing.cap₁ ∩ node.lower).card +
      (saturation.state.packing.cap₂ ∩ node.lower).card +
      (saturation.state.packing.cap₃ ∩ node.lower).card +
      (saturation.cap₅ ∩ node.lower).card +
      (saturation.cap₆ ∩ node.lower).card ≤ 12 := by
  have localMem (cap : Finset (Fin n))
      (hcap : cap ∈ capWitnesses χ support 4)
      (hcapSub : cap ⊆ saturation.capSupport) :
      cap ∈ capWitnesses χ (node.lower ∪ node.upper) 4 := by
    have hcapData := mem_capWitnesses.mp hcap
    exact mem_capWitnesses.mpr ⟨hcapSub.trans hlocal, hcapData.2⟩
  have hregSub : saturation.state.regenerated ⊆ saturation.capSupport := by
    intro x hx
    simp [SixCapSaturation578.capSupport,
      SevenWitnessRegenerationPacking578.fourCapSupport, hx]
  have hcap₁Sub :
      saturation.state.packing.cap₁ ⊆ saturation.capSupport := by
    intro x hx
    simp [SixCapSaturation578.capSupport,
      SevenWitnessRegenerationPacking578.fourCapSupport,
      ThreeDisjointCupCapFourPacking578.capSupport, hx]
  have hcap₂Sub :
      saturation.state.packing.cap₂ ⊆ saturation.capSupport := by
    intro x hx
    simp [SixCapSaturation578.capSupport,
      SevenWitnessRegenerationPacking578.fourCapSupport,
      ThreeDisjointCupCapFourPacking578.capSupport, hx]
  have hcap₃Sub :
      saturation.state.packing.cap₃ ⊆ saturation.capSupport := by
    intro x hx
    simp [SixCapSaturation578.capSupport,
      SevenWitnessRegenerationPacking578.fourCapSupport,
      ThreeDisjointCupCapFourPacking578.capSupport, hx]
  have hcap₅Sub : saturation.cap₅ ⊆ saturation.capSupport := by
    intro x hx
    simp [SixCapSaturation578.capSupport, hx]
  have hcap₆Sub : saturation.cap₆ ⊆ saturation.capSupport := by
    intro x hx
    simp [SixCapSaturation578.capSupport, hx]
  have hregLe := capFour_inter_lower_card_le_two_of_not_subset_lower
    node.deep
    (localMem saturation.state.regenerated saturation.state.regenerated_mem
      hregSub) hregenerated
  have hcap₁Le := capFour_inter_lower_card_le_two_of_not_subset_lower
    node.deep
    (localMem saturation.state.packing.cap₁
      saturation.state.packing.cap₁_mem hcap₁Sub) hcap₁
  have hcap₂Le := capFour_inter_lower_card_le_two_of_not_subset_lower
    node.deep
    (localMem saturation.state.packing.cap₂
      saturation.state.packing.cap₂_mem hcap₂Sub) hcap₂
  have hcap₃Le := capFour_inter_lower_card_le_two_of_not_subset_lower
    node.deep
    (localMem saturation.state.packing.cap₃
      saturation.state.packing.cap₃_mem hcap₃Sub) hcap₃
  have hcap₅Le := capFour_inter_lower_card_le_two_of_not_subset_lower
    node.deep (localMem saturation.cap₅ saturation.cap₅_mem hcap₅Sub) hcap₅
  have hcap₆Le := capFour_inter_lower_card_le_two_of_not_subset_lower
    node.deep (localMem saturation.cap₆ saturation.cap₆_mem hcap₆Sub) hcap₆
  omega

/-- If the six caps demand at least thirteen lower-child incidences at one
local split, then one complete four-cap lies in the lower child. -/
theorem SixCapSaturation578.exists_cap_subset_lower_of_thirteen_le_sum
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (node : DecompositionSplit χ)
    (hlocal : saturation.capSupport ⊆ node.lower ∪ node.upper)
    (hdemand : 13 ≤
      (saturation.state.regenerated ∩ node.lower).card +
        (saturation.state.packing.cap₁ ∩ node.lower).card +
        (saturation.state.packing.cap₂ ∩ node.lower).card +
        (saturation.state.packing.cap₃ ∩ node.lower).card +
        (saturation.cap₅ ∩ node.lower).card +
        (saturation.cap₆ ∩ node.lower).card) :
    saturation.state.regenerated ⊆ node.lower ∨
      saturation.state.packing.cap₁ ⊆ node.lower ∨
      saturation.state.packing.cap₂ ⊆ node.lower ∨
      saturation.state.packing.cap₃ ⊆ node.lower ∨
      saturation.cap₅ ⊆ node.lower ∨ saturation.cap₆ ⊆ node.lower := by
  by_contra hnone
  simp only [not_or] at hnone
  have hle := saturation.sum_cap_inter_lower_card_le_twelve node hlocal
    hnone.1 hnone.2.1 hnone.2.2.1 hnone.2.2.2.1
    hnone.2.2.2.2.1 hnone.2.2.2.2.2
  omega

/-- Exactly eight vertices remain outside the six disjoint four-caps at the
32-vertex gate. -/
theorem SixCapSaturation578.unusedSupport_card_at_32
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support)
    (hcard : support.card = 32) :
    (support \ saturation.capSupport).card = 8 := by
  rw [Finset.card_sdiff_of_subset saturation.capSupport_subset,
    hcard, saturation.capSupport_card]

/-- A four-cup chosen after deleting each one of the 24 vertices occupied by
the six-cap saturation.  The witness may depend on both the deleted vertex and
its membership proof; proof irrelevance makes that dependence immaterial. -/
structure SixCapDeletionCupLedger578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support) where
  cupFor : ∀ x : Fin n, x ∈ saturation.capSupport → Finset (Fin n)
  cupFor_mem : ∀ (x : Fin n) (hx : x ∈ saturation.capSupport),
    cupFor x hx ∈ capWitnesses χ.dual
      (saturation.capSupport \ {x}) 4

/-- Deleting one vertex from the six-cap support leaves a decomposable
23-set, so the exact `32/23` color-dual density supplies a four-cup. -/
theorem SixCapSaturation578.containsCupFour_after_delete
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    {x : Fin n} (hx : x ∈ saturation.capSupport) :
    ContainsCupSet χ (saturation.capSupport \ {x}) 4 := by
  have hsingleton : ({x} : Finset (Fin n)) ⊆ saturation.capSupport := by
    simpa using hx
  have hdeleteCard : (saturation.capSupport \ {x}).card = 23 := by
    rw [Finset.card_sdiff_of_subset hsingleton,
      saturation.capSupport_card]
    simp
  have hdeleteSub : saturation.capSupport \ {x} ⊆ reservoir :=
    Finset.sdiff_subset.trans saturation.capSupport_subset
  have hdeleteDecomposable :
      IsDecomposableOn χ (saturation.capSupport \ {x}) :=
    hreservoir.subset hdeleteSub (Finset.card_pos.mp (by omega))
  exact containsCupFour_of_colorDualLower_large_subset_at_578
    hdeleteDecomposable (by omega) hdeleteSub hnoCap hnoStrong

/-- The full deletion-indexed four-cup ledger on the saturated 24-vertex cap
support. -/
theorem SixCapSaturation578.exists_deletionCupLedger
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    Nonempty (SixCapDeletionCupLedger578 saturation) := by
  classical
  have hexists : ∀ (x : Fin n) (hx : x ∈ saturation.capSupport),
      ∃ cup : Finset (Fin n),
        cup ∈ capWitnesses χ.dual (saturation.capSupport \ {x}) 4 := by
    intro x hx
    obtain ⟨cup, hcupSub, hcupCard, hcupSet⟩ :=
      saturation.containsCupFour_after_delete
        hreservoir hnoCap hnoStrong hx
    exact ⟨cup, mem_capWitnesses.mpr
      ⟨hcupSub, hcupCard, isCapSet_dual_iff.mpr hcupSet⟩⟩
  choose cupFor hcupFor using hexists
  exact ⟨{ cupFor := cupFor, cupFor_mem := hcupFor }⟩

/-- Every ledger witness lies in the 24-vertex cap support and avoids its own
deletion index. -/
theorem SixCapDeletionCupLedger578.cupFor_subset_and_avoids
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {saturation : SixCapSaturation578 χ support}
    (ledger : SixCapDeletionCupLedger578 saturation)
    (x : Fin n) (hx : x ∈ saturation.capSupport) :
    ledger.cupFor x hx ⊆ saturation.capSupport ∧
      x ∉ ledger.cupFor x hx := by
  have hsub := (mem_capWitnesses.mp (ledger.cupFor_mem x hx)).1
  constructor
  · exact hsub.trans Finset.sdiff_subset
  · intro hxCup
    exact (Finset.mem_sdiff.mp (hsub hxCup)).2 (by simp)

/-- A missed cup in the `2+2+0` incidence branch is genuinely disjoint from
the regenerated cap. -/
theorem exists_missedCup_disjoint_of_twoTwoZeroCupIncidence578
    {n : ℕ} {cap cup₁ cup₂ cup₃ : Finset (Fin n)}
    (hincidence : TwoTwoZeroCupIncidence578 cap cup₁ cup₂ cup₃) :
    ∃ cup ∈ ({cup₁, cup₂, cup₃} : Finset (Finset (Fin n))),
      Disjoint cup cap := by
  have disjoint_of_zero (cup : Finset (Fin n))
      (hzero : (cap ∩ cup).card = 0) : Disjoint cup cap := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    have hempty : cap ∩ cup = ∅ := Finset.card_eq_zero.mp hzero
    simpa [Finset.inter_comm] using hempty
  rcases hincidence with hfirst | hsecond | hthird
  · exact ⟨cup₁, by simp, disjoint_of_zero cup₁ hfirst.1⟩
  · exact ⟨cup₂, by simp, disjoint_of_zero cup₂ hsecond.2.1⟩
  · exact ⟨cup₃, by simp, disjoint_of_zero cup₃ hthird.2.2⟩

/-- The protected resource in the `2+2+0` branch: one selected four-cup,
the regenerated plus three external four-caps, and one new residual four-cap
are mutually disjoint. -/
structure ProtectedCupFiveCapPacking578
    {n : ℕ} (χ : TripleColoring n) (support : Finset (Fin n)) where
  state : SevenWitnessRegenerationPacking578 χ support
  protectedCup : Finset (Fin n)
  protectedCup_mem : protectedCup ∈ capWitnesses χ.dual support 4
  protectedCup_fourCapSupport :
    Disjoint protectedCup state.fourCapSupport
  cap₅ : Finset (Fin n)
  cap₅_mem : cap₅ ∈ capWitnesses χ support 4
  cap₅_priorSupport :
    Disjoint cap₅ (protectedCup ∪ state.fourCapSupport)

/-- The 24 vertices occupied by the protected cup and five caps. -/
def ProtectedCupFiveCapPacking578.selectedSupport
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ProtectedCupFiveCapPacking578 χ support) :
    Finset (Fin n) :=
  packing.protectedCup ∪ packing.state.fourCapSupport ∪ packing.cap₅

theorem ProtectedCupFiveCapPacking578.selectedSupport_subset
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ProtectedCupFiveCapPacking578 χ support) :
    packing.selectedSupport ⊆ support := by
  exact Finset.union_subset
    (Finset.union_subset
      (mem_capWitnesses.mp packing.protectedCup_mem).1
      packing.state.fourCapSupport_subset)
    (mem_capWitnesses.mp packing.cap₅_mem).1

theorem ProtectedCupFiveCapPacking578.selectedSupport_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ProtectedCupFiveCapPacking578 χ support) :
    packing.selectedSupport.card = 24 := by
  have hfirst : Disjoint packing.protectedCup
      packing.state.fourCapSupport := packing.protectedCup_fourCapSupport
  have hlast : Disjoint
      (packing.protectedCup ∪ packing.state.fourCapSupport) packing.cap₅ :=
    packing.cap₅_priorSupport.symm
  rw [ProtectedCupFiveCapPacking578.selectedSupport,
    Finset.card_union_of_disjoint hlast,
    Finset.card_union_of_disjoint hfirst,
    (mem_capWitnesses.mp packing.protectedCup_mem).2.1,
    packing.state.fourCapSupport_card,
    (mem_capWitnesses.mp packing.cap₅_mem).2.1]

theorem ProtectedCupFiveCapPacking578.unusedSupport_card_at_32
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ProtectedCupFiveCapPacking578 χ support)
    (hcard : support.card = 32) :
    (support \ packing.selectedSupport).card = 8 := by
  rw [Finset.card_sdiff_of_subset packing.selectedSupport_subset,
    hcard, packing.selectedSupport_card]

/-- The `2+2+0` branch of the exact seven-witness gate yields the protected
one-cup/five-cap packing and an eight-vertex remainder. -/
theorem SevenWitnessRegenerationPacking578.exists_protectedCupFiveCapPacking
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hincidence : TwoTwoZeroCupIncidence578 state.regenerated
      state.packing.cup₁ state.packing.cup₂ state.packing.cup₃)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    Nonempty (ProtectedCupFiveCapPacking578 χ reservoir) := by
  obtain ⟨protectedCup, hprotectedSelected, hprotectedRegenerated⟩ :=
    exists_missedCup_disjoint_of_twoTwoZeroCupIncidence578 hincidence
  have hprotectedMem : protectedCup ∈ capWitnesses χ.dual reservoir 4 := by
    rcases Finset.mem_insert.mp hprotectedSelected with hcup₁ | hrest
    · subst protectedCup
      exact state.packing.cup₁_mem
    · rcases Finset.mem_insert.mp hrest with hcup₂ | hcup₃
      · subst protectedCup
        exact state.packing.cup₂_mem
      · have hcup₃Eq : protectedCup = state.packing.cup₃ :=
          Finset.mem_singleton.mp hcup₃
        subst protectedCup
        exact state.packing.cup₃_mem
  have hprotectedCupSupport : protectedCup ⊆ state.packing.cupSupport := by
    intro x hx
    rcases Finset.mem_insert.mp hprotectedSelected with hcup₁ | hrest
    · subst protectedCup
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · rcases Finset.mem_insert.mp hrest with hcup₂ | hcup₃
      · subst protectedCup
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
      · have hcup₃Eq : protectedCup = state.packing.cup₃ :=
          Finset.mem_singleton.mp hcup₃
        subst protectedCup
        exact Finset.mem_union_right _ hx
  have hprotectedExternal :
      Disjoint protectedCup state.packing.capSupport :=
    state.packing.colors_disjoint.mono hprotectedCupSupport Finset.Subset.rfl
  have hprotectedFour : Disjoint protectedCup state.fourCapSupport := by
    rw [SevenWitnessRegenerationPacking578.fourCapSupport,
      Finset.disjoint_union_right]
    exact ⟨hprotectedRegenerated, hprotectedExternal⟩
  let priorSupport := protectedCup ∪ state.fourCapSupport
  have hpriorSub : priorSupport ⊆ reservoir :=
    Finset.union_subset (mem_capWitnesses.mp hprotectedMem).1
      state.fourCapSupport_subset
  have hpriorCard : priorSupport.card = 20 := by
    rw [Finset.card_union_of_disjoint hprotectedFour,
      (mem_capWitnesses.mp hprotectedMem).2.1,
      state.fourCapSupport_card]
  let rest := reservoir \ priorSupport
  have hrestCard : rest.card = 12 := by
    rw [Finset.card_sdiff_of_subset hpriorSub, hcard, hpriorCard]
  have hrestDecomposable : IsDecomposableOn χ rest :=
    hreservoir.subset Finset.sdiff_subset (Finset.card_pos.mp (by omega))
  obtain ⟨cap₅, hcap₅Rest, hcap₅Card, hcap₅Set⟩ :=
    containsCapFour_of_predecessor_458 h458 hrestDecomposable
      (by omega) Finset.sdiff_subset hnoCup hnoStrong
  have hcap₅Support : cap₅ ⊆ reservoir :=
    hcap₅Rest.trans Finset.sdiff_subset
  have hcap₅Prior : Disjoint cap₅ priorSupport := by
    rw [Finset.disjoint_left]
    intro x hxCap₅ hxPrior
    exact (Finset.mem_sdiff.mp (hcap₅Rest hxCap₅)).2 hxPrior
  exact ⟨{
    state := state
    protectedCup := protectedCup
    protectedCup_mem := hprotectedMem
    protectedCup_fourCapSupport := hprotectedFour
    cap₅ := cap₅
    cap₅_mem := mem_capWitnesses.mpr
      ⟨hcap₅Support, hcap₅Card, hcap₅Set⟩
    cap₅_priorSupport := hcap₅Prior
  }⟩

/-- The still-open all-hit branch retains the complete seven-witness state
together with its exact `2+1+1` incidence certificate. -/
structure AllHitSevenWitnessPacking578
    {n : ℕ} (χ : TripleColoring n) (support : Finset (Fin n)) where
  state : SevenWitnessRegenerationPacking578 χ support
  incidence : TwoOneOneCupIncidence578 state.regenerated
    state.packing.cup₁ state.packing.cup₂ state.packing.cup₃

/-- Exact profile-sensitive reconnect: the live singleton-root gate either
produces a protected disjoint one-cup/five-cap packing with eight unused
vertices, or it enters the explicitly retained all-hit `2+1+1` state. -/
theorem exists_protectedCupFiveCapPacking_or_allHit_of_colorDualLower_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    Nonempty (ProtectedCupFiveCapPacking578 χ reservoir) ∨
      Nonempty (AllHitSevenWitnessPacking578 χ reservoir) := by
  obtain ⟨state⟩ :=
    exists_sevenWitnessRegenerationPacking_of_colorDualLower_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong
  rcases state.incidence with htwoTwo | htwoOneOne
  · left
    exact state.exists_protectedCupFiveCapPacking
      h458 hreservoir hcard htwoTwo hnoCup hnoStrong
  · exact Or.inr ⟨{ state := state, incidence := htwoOneOne }⟩

/-- A transversal of four-cups, represented through cap witnesses of the dual
coloring. -/
def IsCupWitnessTransversal578
    {n : ℕ} (χ : TripleColoring n)
    (support transversal : Finset (Fin n)) (u : ℕ) : Prop :=
  IsCapWitnessTransversal χ.dual support transversal u

/-- Global consequence of the exact `32/23` density: every transversal of all
reservoir four-cups contains at least ten vertices. -/
theorem ten_le_fourCupTransversal_of_colorDualLower_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir transversal : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8)
    (htransversal :
      IsCupWitnessTransversal578 χ reservoir transversal 4) :
    10 ≤ transversal.card := by
  have hdense : ∀ subset : Finset (Fin n), subset ⊆ reservoir →
      subset.card = 23 → ContainsCapSet χ.dual subset 4 := by
    intro subset hsubset hsubsetCard
    apply containsCapSet_dual_iff.mpr
    exact containsCupFour_of_colorDualLower_large_subset_at_578
      (hreservoir.subset hsubset (Finset.card_pos.mp (by omega)))
      (by omega) hsubset hnoCap hnoStrong
  exact ten_le_capWitnessTransversal_at_578 hcard hdense htransversal

/-- Exact closure target exposed by the density theorem: the live reservoir
cannot have a four-cup transversal of cardinality at most nine.  A future
tree argument producing such a transversal would therefore close this gate. -/
theorem not_exists_nine_fourCupTransversal_of_colorDualLower_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ¬∃ transversal : Finset (Fin n),
      IsCupWitnessTransversal578 χ reservoir transversal 4 ∧
        transversal.card ≤ 9 := by
  rintro ⟨transversal, htransversal, hsmall⟩
  have hlarge := ten_le_fourCupTransversal_of_colorDualLower_at_578
    hreservoir hcard hnoCap hnoStrong htransversal
  omega

/-- A private four-witness for a ten-vertex subtransversal of a twelve-vertex
set must use at least one vertex outside that set. -/
theorem privateFourWitness_has_outside_of_ten_le_of_ambient_card_twelve
    {α : Type*} [DecidableEq α]
    {ambient transversal witness : Finset α} {x : α}
    (htransversalSub : transversal ⊆ ambient)
    (hambientCard : ambient.card = 12)
    (htransversalCard : 10 ≤ transversal.card)
    (hwitnessCard : witness.card = 4)
    (hxWitness : x ∈ witness)
    (hprivate : transversal ∩ witness = {x}) :
    (witness \ ambient).Nonempty := by
  by_contra houtside
  have hwitnessSub : witness ⊆ ambient := by
    intro y hyWitness
    by_contra hyAmbient
    exact houtside ⟨y, Finset.mem_sdiff.mpr ⟨hyWitness, hyAmbient⟩⟩
  have heraseSub : witness.erase x ⊆ ambient \ transversal := by
    intro y hyErase
    have hyWitness := (Finset.mem_erase.mp hyErase).2
    have hyNe : y ≠ x := (Finset.mem_erase.mp hyErase).1
    refine Finset.mem_sdiff.mpr ⟨hwitnessSub hyWitness, ?_⟩
    intro hyTransversal
    have hyPrivate : y ∈ ({x} : Finset α) := by
      rw [← hprivate]
      exact Finset.mem_inter.mpr ⟨hyTransversal, hyWitness⟩
    exact hyNe (Finset.mem_singleton.mp hyPrivate)
  have heraseCard : (witness.erase x).card = 3 := by
    rw [Finset.card_erase_of_mem hxWitness, hwitnessCard]
  have hcomplementCard : (ambient \ transversal).card ≤ 2 := by
    rw [Finset.card_sdiff_of_subset htransversalSub, hambientCard]
    omega
  have hle := Finset.card_le_card heraseSub
  omega

/-- Density applied to the original twelve cup vertices yields a genuinely
global dichotomy.  Either a fourth four-cup avoids all three selected cups, or
a minimum subtransversal of those twelve vertices has between ten and twelve
owners, each with a private four-cup meeting it exactly at that owner. -/
theorem SevenWitnessRegenerationPacking578.exists_fourthDisjointCup_or_privateCupLedger
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    (∃ cup, cup ∈ capWitnesses χ.dual reservoir 4 ∧
      Disjoint cup state.packing.cupSupport) ∨
    ∃ transversal,
      transversal ⊆ state.packing.cupSupport ∧
      10 ≤ transversal.card ∧ transversal.card ≤ 12 ∧
      IsCupWitnessTransversal578 χ reservoir transversal 4 ∧
      ∀ x ∈ transversal, ∃ cup,
        cup ∈ capWitnesses χ.dual reservoir 4 ∧
        transversal ∩ cup = {x} ∧
        (cup \ state.packing.cupSupport).Nonempty := by
  have hcupSupportSub : state.packing.cupSupport ⊆ reservoir := by
    have hcup₁ := (mem_capWitnesses.mp state.packing.cup₁_mem).1
    have hcup₂ := (mem_capWitnesses.mp state.packing.cup₂_mem).1
    have hcup₃ := (mem_capWitnesses.mp state.packing.cup₃_mem).1
    exact Finset.union_subset (Finset.union_subset hcup₁ hcup₂) hcup₃
  by_cases htransversal : IsCupWitnessTransversal578 χ reservoir
      state.packing.cupSupport 4
  · right
    have hhits : HitsEveryFourCapDisjointFrom χ.dual reservoir ∅
        state.packing.cupSupport := by
      intro cup hcup _ hdisjoint
      exact htransversal.2 cup hcup hdisjoint.symm
    obtain ⟨transversal, htransversalSub, htransversalHits, hprivate⟩ :=
      exists_minimal_residualCapTransversal_with_private_caps hhits
    have htransversalCup :
        IsCupWitnessTransversal578 χ reservoir transversal 4 := by
      refine ⟨htransversalSub.trans hcupSupportSub, ?_⟩
      intro cup hcup hdisjoint
      exact htransversalHits cup hcup (by simp) hdisjoint.symm
    have hlarge : 10 ≤ transversal.card :=
      ten_le_fourCupTransversal_of_colorDualLower_at_578
        hreservoir hcard hnoCap hnoStrong htransversalCup
    have hsmall : transversal.card ≤ 12 := by
      have hle := Finset.card_le_card htransversalSub
      rw [state.packing.cupSupport_card] at hle
      exact hle
    refine ⟨transversal, htransversalSub, hlarge, hsmall,
      htransversalCup, ?_⟩
    intro x hx
    obtain ⟨cup, hcup, _, hxCup, hprivateCup⟩ := hprivate x hx
    have hinter :=
      privateCap_inter_transversal_eq_singleton hx hxCup hprivateCup
    have houtside :=
      privateFourWitness_has_outside_of_ten_le_of_ambient_card_twelve
        htransversalSub state.packing.cupSupport_card hlarge
        (mem_capWitnesses.mp hcup).2.1 hxCup hinter
    exact ⟨cup, hcup, hinter, houtside⟩
  · left
    have hnotHits : ¬∀ cup, cup ∈ capWitnesses χ.dual reservoir 4 →
        ¬Disjoint cup state.packing.cupSupport := by
      intro hhits
      exact htransversal ⟨hcupSupportSub, hhits⟩
    push Not at hnotHits
    obtain ⟨cup, hcup, hdisjoint⟩ := hnotHits
    exact ⟨cup, hcup, hdisjoint⟩

/-- A chosen version of the minimum private-cup ledger. -/
structure PrivateCupLedger578
    {n : ℕ} {χ : TripleColoring n} {reservoir : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ reservoir) where
  transversal : Finset (Fin n)
  transversal_sub : transversal ⊆ state.packing.cupSupport
  ten_le : 10 ≤ transversal.card
  card_le_twelve : transversal.card ≤ 12
  transversal_hits :
    IsCupWitnessTransversal578 χ reservoir transversal 4
  cupFor : ∀ x : Fin n, x ∈ transversal → Finset (Fin n)
  cupFor_mem : ∀ (x : Fin n) (hx : x ∈ transversal),
    cupFor x hx ∈ capWitnesses χ.dual reservoir 4
  cupFor_private : ∀ (x : Fin n) (hx : x ∈ transversal),
    transversal ∩ cupFor x hx = {x}
  cupFor_outside : ∀ (x : Fin n) (hx : x ∈ transversal),
    (cupFor x hx \ state.packing.cupSupport).Nonempty

/-- Distinct owners have distinct private four-cups. -/
theorem PrivateCupLedger578.cupFor_injective
    {n : ℕ} {χ : TripleColoring n} {reservoir : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ reservoir}
    (ledger : PrivateCupLedger578 state)
    {x y : Fin n} (hx : x ∈ ledger.transversal)
    (hy : y ∈ ledger.transversal)
    (heq : ledger.cupFor x hx = ledger.cupFor y hy) :
    x = y := by
  have hsingle : ({x} : Finset (Fin n)) = {y} := by
    rw [← ledger.cupFor_private x hx,
      ← ledger.cupFor_private y hy, heq]
  simpa using hsingle

/-- Package the private witnesses into an owner-indexed injective ledger. -/
theorem SevenWitnessRegenerationPacking578.exists_fourthDisjointCup_or_privateCupLedgerPackage
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    (∃ cup, cup ∈ capWitnesses χ.dual reservoir 4 ∧
      Disjoint cup state.packing.cupSupport) ∨
      Nonempty (PrivateCupLedger578 state) := by
  rcases state.exists_fourthDisjointCup_or_privateCupLedger
      hreservoir hcard hnoCap hnoStrong with hfourth | hledger
  · exact Or.inl hfourth
  · right
    obtain ⟨transversal, hsub, hten, htwelve, hhits, hprivate⟩ := hledger
    choose cupFor hcupFor hcupPrivate hcupOutside using hprivate
    exact ⟨{
      transversal := transversal
      transversal_sub := hsub
      ten_le := hten
      card_le_twelve := htwelve
      transversal_hits := hhits
      cupFor := cupFor
      cupFor_mem := hcupFor
      cupFor_private := hcupPrivate
      cupFor_outside := hcupOutside
    }⟩

/-- Reconnect the fourth-cup/private-ledger dichotomy to the exact
32-vertex singleton-root gate. -/
theorem exists_sevenWitness_with_fourthDisjointCup_or_privateCupLedger_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ∃ state : SevenWitnessRegenerationPacking578 χ reservoir,
      (∃ cup, cup ∈ capWitnesses χ.dual reservoir 4 ∧
        Disjoint cup state.packing.cupSupport) ∨
        Nonempty (PrivateCupLedger578 state) := by
  obtain ⟨state⟩ :=
    exists_sevenWitnessRegenerationPacking_of_colorDualLower_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong
  exact ⟨state,
    state.exists_fourthDisjointCup_or_privateCupLedgerPackage
      hreservoir hcard hnoCap hnoStrong⟩

/-- Spend the strict `(4,5,8)` predecessor twice on the complement of the
four caps already present in a seven-witness state. -/
theorem SevenWitnessRegenerationPacking578.exists_sixCapSaturation
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    Nonempty (SixCapSaturation578 χ reservoir) := by
  let rest₁ := reservoir \ state.fourCapSupport
  have hrest₁Card : rest₁.card = 16 := by
    rw [Finset.card_sdiff_of_subset state.fourCapSupport_subset,
      hcard, state.fourCapSupport_card]
  have hrest₁Decomposable : IsDecomposableOn χ rest₁ :=
    hreservoir.subset Finset.sdiff_subset (Finset.card_pos.mp (by omega))
  obtain ⟨cap₅, hcap₅Rest₁, hcap₅Card, hcap₅⟩ :=
    containsCapFour_of_predecessor_458 h458 hrest₁Decomposable
      (by omega) Finset.sdiff_subset hnoCup hnoStrong
  have hcap₅Support : cap₅ ⊆ reservoir :=
    hcap₅Rest₁.trans Finset.sdiff_subset
  let rest₂ := rest₁ \ cap₅
  have hrest₂Card : rest₂.card = 12 := by
    rw [Finset.card_sdiff_of_subset hcap₅Rest₁, hrest₁Card, hcap₅Card]
  have hrest₂Decomposable : IsDecomposableOn χ rest₂ :=
    hrest₁Decomposable.subset Finset.sdiff_subset
      (Finset.card_pos.mp (by omega))
  obtain ⟨cap₆, hcap₆Rest₂, hcap₆Card, hcap₆⟩ :=
    containsCapFour_of_predecessor_458 h458 hrest₂Decomposable
      (by omega) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      hnoCup hnoStrong
  have hcap₆Rest₁ : cap₆ ⊆ rest₁ :=
    hcap₆Rest₂.trans Finset.sdiff_subset
  have hcap₆Support : cap₆ ⊆ reservoir :=
    hcap₆Rest₁.trans Finset.sdiff_subset
  have hcap₅Four : Disjoint cap₅ state.fourCapSupport := by
    rw [Finset.disjoint_left]
    intro x hxCap₅ hxFour
    exact (Finset.mem_sdiff.mp (hcap₅Rest₁ hxCap₅)).2 hxFour
  have hcap₆Four : Disjoint cap₆ state.fourCapSupport := by
    rw [Finset.disjoint_left]
    intro x hxCap₆ hxFour
    exact (Finset.mem_sdiff.mp (hcap₆Rest₁ hxCap₆)).2 hxFour
  have hcap₅Cap₆ : Disjoint cap₅ cap₆ := by
    rw [Finset.disjoint_left]
    intro x hxCap₅ hxCap₆
    exact (Finset.mem_sdiff.mp (hcap₆Rest₂ hxCap₆)).2 hxCap₅
  exact ⟨{
    state := state
    cap₅ := cap₅
    cap₆ := cap₆
    cap₅_mem := mem_capWitnesses.mpr ⟨hcap₅Support, hcap₅Card, hcap₅⟩
    cap₆_mem := mem_capWitnesses.mpr ⟨hcap₆Support, hcap₆Card, hcap₆⟩
    cap₅_fourCapSupport := hcap₅Four
    cap₆_fourCapSupport := hcap₆Four
    cap₅_cap₆ := hcap₅Cap₆
  }⟩

/-- The exact state-578 singleton-root gate yields six pairwise-disjoint
four-caps occupying 24 reservoir vertices and hence leaves exactly eight
vertices unused. -/
theorem exists_sixCapSaturation_of_colorDualLower_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    Nonempty (SixCapSaturation578 χ reservoir) := by
  obtain ⟨state⟩ :=
    exists_sevenWitnessRegenerationPacking_of_colorDualLower_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong
  exact state.exists_sixCapSaturation
    h458 hreservoir hcard hnoCup hnoStrong

end ErdosSzekeres

end
