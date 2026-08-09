module

public import ErdosSzekeres.StructuralChargingNextState578DualPacking
public import ErdosSzekeres.StructuralChargingTreeAllocation
public import ErdosSzekeres.Decomposable
import ErdosSzekeres.StructuralChargingNextState578SpanCounterexample

@[expose] public section

/-!
# The three-cup regeneration obstruction at state 578

The color-dual 32-vertex gate supplies three disjoint four-cups and a new
four-cap inside their 12-vertex union.  This file isolates that smaller
configuration and records its exact incidence alternatives before using the
recursive decomposition tree.
-/

namespace ErdosSzekeres

/-- A four-cap has `2+2+0` incidence with three selected cups when it misses
one cup and uses two vertices from each of the other two. -/
def TwoTwoZeroCupIncidence578
    {n : ℕ} (cap cup₁ cup₂ cup₃ : Finset (Fin n)) : Prop :=
  ((cap ∩ cup₁).card = 0 ∧ (cap ∩ cup₂).card = 2 ∧
      (cap ∩ cup₃).card = 2) ∨
    ((cap ∩ cup₁).card = 2 ∧ (cap ∩ cup₂).card = 0 ∧
      (cap ∩ cup₃).card = 2) ∨
    ((cap ∩ cup₁).card = 2 ∧ (cap ∩ cup₂).card = 2 ∧
      (cap ∩ cup₃).card = 0)

/-- The complete 12-vertex obstruction retained after regenerating a cap
inside three disjoint four-cups. -/
structure ThreeCupRegenerationConfiguration578
    {n : ℕ} (χ : TripleColoring n) (support : Finset (Fin n)) where
  cup₁ : Finset (Fin n)
  cup₂ : Finset (Fin n)
  cup₃ : Finset (Fin n)
  cap : Finset (Fin n)
  cup₁_mem : cup₁ ∈ capWitnesses χ.dual support 4
  cup₂_mem : cup₂ ∈ capWitnesses χ.dual support 4
  cup₃_mem : cup₃ ∈ capWitnesses χ.dual support 4
  cap_mem : cap ∈ capWitnesses χ support 4
  cup₁_cup₂ : Disjoint cup₁ cup₂
  cup₁_cup₃ : Disjoint cup₁ cup₃
  cup₂_cup₃ : Disjoint cup₂ cup₃
  support_eq : support = cup₁ ∪ cup₂ ∪ cup₃

/-- Three disjoint cups partition the cardinality of every subset of their
union into its three intersection cardinalities. -/
theorem card_eq_cup_intersections_of_subset_union
    {n : ℕ} {subset cup₁ cup₂ cup₃ : Finset (Fin n)}
    (hcup₁Cup₂ : Disjoint cup₁ cup₂)
    (hcup₁Cup₃ : Disjoint cup₁ cup₃)
    (hcup₂Cup₃ : Disjoint cup₂ cup₃)
    (hsubset : subset ⊆ cup₁ ∪ cup₂ ∪ cup₃) :
    subset.card = (subset ∩ cup₁).card + (subset ∩ cup₂).card +
      (subset ∩ cup₃).card := by
  exact card_eq_three_inter_of_subset_union
    hcup₁Cup₂ hcup₁Cup₃ hcup₂Cup₃ hsubset

/-- A four-set contained in three disjoint blocks, meeting each block in at
most two vertices, has exactly one of the two integer profiles `2+2+0` or
`2+1+1`. -/
theorem twoTwoZero_or_twoOneOne_of_card_eq_four
    {n : ℕ} {cap cup₁ cup₂ cup₃ : Finset (Fin n)}
    (hcard : cap.card = 4)
    (hcup₁Cup₂ : Disjoint cup₁ cup₂)
    (hcup₁Cup₃ : Disjoint cup₁ cup₃)
    (hcup₂Cup₃ : Disjoint cup₂ cup₃)
    (hsub : cap ⊆ cup₁ ∪ cup₂ ∪ cup₃)
    (hinter₁ : (cap ∩ cup₁).card ≤ 2)
    (hinter₂ : (cap ∩ cup₂).card ≤ 2)
    (hinter₃ : (cap ∩ cup₃).card ≤ 2) :
    TwoTwoZeroCupIncidence578 cap cup₁ cup₂ cup₃ ∨
      TwoOneOneCupIncidence578 cap cup₁ cup₂ cup₃ := by
  have hpartition := card_eq_cup_intersections_of_subset_union
    hcup₁Cup₂ hcup₁Cup₃ hcup₂Cup₃ hsub
  rw [hcard] at hpartition
  simp only [TwoTwoZeroCupIncidence578, TwoOneOneCupIncidence578]
  omega

/-- Every regenerated cap in a three-cup configuration has the exhaustive
`2+2+0` versus `2+1+1` incidence classification. -/
theorem ThreeCupRegenerationConfiguration578.incidence
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (configuration : ThreeCupRegenerationConfiguration578 χ support) :
    TwoTwoZeroCupIncidence578 configuration.cap
        configuration.cup₁ configuration.cup₂ configuration.cup₃ ∨
      TwoOneOneCupIncidence578 configuration.cap
        configuration.cup₁ configuration.cup₂ configuration.cup₃ := by
  have hcup₁Data := mem_capWitnesses.mp configuration.cup₁_mem
  have hcup₂Data := mem_capWitnesses.mp configuration.cup₂_mem
  have hcup₃Data := mem_capWitnesses.mp configuration.cup₃_mem
  have hcapData := mem_capWitnesses.mp configuration.cap_mem
  apply twoTwoZero_or_twoOneOne_of_card_eq_four
    hcapData.2.1 configuration.cup₁_cup₂ configuration.cup₁_cup₃
    configuration.cup₂_cup₃
  · simpa [configuration.support_eq] using hcapData.1
  · exact inter_card_le_two_of_cup_cap
      (isCapSet_dual_iff.mp hcup₁Data.2.2) hcapData.2.2
  · exact inter_card_le_two_of_cup_cap
      (isCapSet_dual_iff.mp hcup₂Data.2.2) hcapData.2.2
  · exact inter_card_le_two_of_cup_cap
      (isCapSet_dual_iff.mp hcup₃Data.2.2) hcapData.2.2

/-- A three-cup regeneration configuration together with an explicit recursive
decomposition tree of its 12-vertex support. -/
structure ThreeCupRegenerationTree578
    {n : ℕ} (χ : TripleColoring n) (support : Finset (Fin n)) where
  configuration : ThreeCupRegenerationConfiguration578 χ support
  tree : DecompositionTree χ support

/-- The exact support cardinality of a three-cup regeneration configuration. -/
theorem ThreeCupRegenerationConfiguration578.support_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (configuration : ThreeCupRegenerationConfiguration578 χ support) :
    support.card = 12 := by
  have hcup₁Data := mem_capWitnesses.mp configuration.cup₁_mem
  have hcup₂Data := mem_capWitnesses.mp configuration.cup₂_mem
  have hcup₃Data := mem_capWitnesses.mp configuration.cup₃_mem
  have hcup₁₂Cup₃ : Disjoint (configuration.cup₁ ∪ configuration.cup₂)
      configuration.cup₃ :=
    Finset.disjoint_union_left.mpr
      ⟨configuration.cup₁_cup₃, configuration.cup₂_cup₃⟩
  rw [configuration.support_eq,
    Finset.card_union_of_disjoint hcup₁₂Cup₃,
    Finset.card_union_of_disjoint configuration.cup₁_cup₂,
    hcup₁Data.2.1, hcup₂Data.2.1, hcup₃Data.2.1]

/-- The twelve vertices occupied by the three selected cups. -/
def ThreeDisjointCupCapFourPacking578.cupSupport
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    Finset (Fin n) :=
  packing.cup₁ ∪ packing.cup₂ ∪ packing.cup₃

/-- The twelve vertices occupied by the three external selected caps. -/
def ThreeDisjointCupCapFourPacking578.capSupport
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    Finset (Fin n) :=
  packing.cap₁ ∪ packing.cap₂ ∪ packing.cap₃

/-- The full 24-vertex support occupied by the global `3+3` packing. -/
def ThreeDisjointCupCapFourPacking578.selectedSupport
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    Finset (Fin n) :=
  packing.cupSupport ∪ packing.capSupport

theorem ThreeDisjointCupCapFourPacking578.cupSupport_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    packing.cupSupport.card = 12 := by
  have hcup₁Data := mem_capWitnesses.mp packing.cup₁_mem
  have hcup₂Data := mem_capWitnesses.mp packing.cup₂_mem
  have hcup₃Data := mem_capWitnesses.mp packing.cup₃_mem
  have hcup₁₂Cup₃ : Disjoint (packing.cup₁ ∪ packing.cup₂) packing.cup₃ :=
    Finset.disjoint_union_left.mpr
      ⟨packing.cup₁_cup₃, packing.cup₂_cup₃⟩
  rw [ThreeDisjointCupCapFourPacking578.cupSupport,
    Finset.card_union_of_disjoint hcup₁₂Cup₃,
    Finset.card_union_of_disjoint packing.cup₁_cup₂,
    hcup₁Data.2.1, hcup₂Data.2.1, hcup₃Data.2.1]

theorem ThreeDisjointCupCapFourPacking578.capSupport_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    packing.capSupport.card = 12 := by
  have hcap₁Data := mem_capWitnesses.mp packing.cap₁_mem
  have hcap₂Data := mem_capWitnesses.mp packing.cap₂_mem
  have hcap₃Data := mem_capWitnesses.mp packing.cap₃_mem
  have hcap₁₂Cap₃ : Disjoint (packing.cap₁ ∪ packing.cap₂) packing.cap₃ :=
    Finset.disjoint_union_left.mpr
      ⟨packing.cap₁_cap₃, packing.cap₂_cap₃⟩
  rw [ThreeDisjointCupCapFourPacking578.capSupport,
    Finset.card_union_of_disjoint hcap₁₂Cap₃,
    Finset.card_union_of_disjoint packing.cap₁_cap₂,
    hcap₁Data.2.1, hcap₂Data.2.1, hcap₃Data.2.1]

theorem ThreeDisjointCupCapFourPacking578.selectedSupport_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    packing.selectedSupport.card = 24 := by
  have hcup := packing.cupSupport_card
  have hcap := packing.capSupport_card
  change (packing.cup₁ ∪ packing.cup₂ ∪ packing.cup₃).card = 12 at hcup
  change (packing.cap₁ ∪ packing.cap₂ ∪ packing.cap₃).card = 12 at hcap
  change ((packing.cup₁ ∪ packing.cup₂ ∪ packing.cup₃) ∪
    (packing.cap₁ ∪ packing.cap₂ ∪ packing.cap₃)).card = 24
  rw [
    Finset.card_union_of_disjoint packing.colors_disjoint,
    hcup, hcap]

theorem ThreeDisjointCupCapFourPacking578.selectedSupport_subset
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support) :
    packing.selectedSupport ⊆ support := by
  have hcup₁ := (mem_capWitnesses.mp packing.cup₁_mem).1
  have hcup₂ := (mem_capWitnesses.mp packing.cup₂_mem).1
  have hcup₃ := (mem_capWitnesses.mp packing.cup₃_mem).1
  have hcap₁ := (mem_capWitnesses.mp packing.cap₁_mem).1
  have hcap₂ := (mem_capWitnesses.mp packing.cap₂_mem).1
  have hcap₃ := (mem_capWitnesses.mp packing.cap₃_mem).1
  exact Finset.union_subset
    (Finset.union_subset (Finset.union_subset hcup₁ hcup₂) hcup₃)
    (Finset.union_subset (Finset.union_subset hcap₁ hcap₂) hcap₃)

/-- Exactly eight reservoir vertices remain outside the selected `3+3`
packing at the live 32-vertex gate. -/
theorem ThreeDisjointCupCapFourPacking578.unusedSupport_card_at_32
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support)
    (hcard : support.card = 32) :
    (support \ packing.selectedSupport).card = 8 := by
  rw [Finset.card_sdiff_of_subset packing.selectedSupport_subset,
    hcard, packing.selectedSupport_card]

/-- The full surviving witness package after regeneration.  Unlike the local
12-vertex configuration, this retains the three external disjoint caps. -/
structure SevenWitnessRegenerationPacking578
    {n : ℕ} (χ : TripleColoring n) (support : Finset (Fin n)) where
  packing : ThreeDisjointCupCapFourPacking578 χ support
  regenerated : Finset (Fin n)
  regenerated_mem : regenerated ∈ capWitnesses χ support 4
  regenerated_sub : regenerated ⊆ packing.cupSupport

/-- The root profile of a four-cup at a deep split.  If it reaches the lower
child, at most two of its vertices lie in the upper child and all such upper
vertices are sweep endpoints of the cup. -/
def CupFourRootProfile578
    {n : ℕ} (cup lower upper : Finset (Fin n)) : Prop :=
  cup ⊆ lower ∪ upper ∧
    ((cup ∩ lower).Nonempty →
      (cup ∩ upper).card ≤ 2 ∧
        ∀ q ∈ cup ∩ upper, HasDeepBelowSplit.IsSweepEndpoint cup q)

/-- The color-dual root profile of a four-cap.  If it reaches the upper child,
at most two vertices lie in the lower child and all such lower vertices are
sweep endpoints of the cap. -/
def CapFourRootProfile578
    {n : ℕ} (cap lower upper : Finset (Fin n)) : Prop :=
  cap ⊆ lower ∪ upper ∧
    ((cap ∩ upper).Nonempty →
      (cap ∩ lower).card ≤ 2 ∧
        ∀ q ∈ cap ∩ lower, HasDeepBelowSplit.IsSweepEndpoint cap q)

/-- Aggregate root data for all four selected witnesses. -/
structure ThreeCupRegenerationRootProfile578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (configuration : ThreeCupRegenerationConfiguration578 χ support)
    (node : DecompositionSplit χ) : Prop where
  support_sub : support ⊆ node.lower ∪ node.upper
  cup₁ : CupFourRootProfile578 configuration.cup₁ node.lower node.upper
  cup₂ : CupFourRootProfile578 configuration.cup₂ node.lower node.upper
  cup₃ : CupFourRootProfile578 configuration.cup₃ node.lower node.upper
  cap : CapFourRootProfile578 configuration.cap node.lower node.upper

/-- Every split containing a three-cup regeneration support carries the
aggregate asymmetric cup/cap root profile. -/
theorem ThreeCupRegenerationConfiguration578.rootProfile
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (configuration : ThreeCupRegenerationConfiguration578 χ support)
    (node : DecompositionSplit χ)
    (hsupport : support ⊆ node.lower ∪ node.upper) :
    ThreeCupRegenerationRootProfile578 configuration node := by
  have cupProfile (cup : Finset (Fin n))
      (hcup : cup ∈ capWitnesses χ.dual support 4) :
      CupFourRootProfile578 cup node.lower node.upper := by
    have hcupData := mem_capWitnesses.mp hcup
    have hcupSub : cup ⊆ node.lower ∪ node.upper := hcupData.1.trans hsupport
    have hcupSet : IsCupSet χ cup := isCapSet_dual_iff.mp hcupData.2.2
    refine ⟨hcupSub, fun hcupLower ↦ ⟨?_, ?_⟩⟩
    · exact node.deep.cup_inter_upper_card_le_two hcupSub hcupSet hcupLower
    · intro q hq
      exact node.deep.upper_mem_cup_isSweepEndpoint hcupSub hcupSet hcupLower
        (Finset.mem_inter.mp hq).1 (Finset.mem_inter.mp hq).2
  have capProfile (cap : Finset (Fin n))
      (hcap : cap ∈ capWitnesses χ support 4) :
      CapFourRootProfile578 cap node.lower node.upper := by
    have hcapData := mem_capWitnesses.mp hcap
    have hcapSub : cap ⊆ node.lower ∪ node.upper := hcapData.1.trans hsupport
    refine ⟨hcapSub, fun hcapUpper ↦ ⟨?_, ?_⟩⟩
    · exact node.deep.cap_inter_lower_card_le_two
        hcapSub hcapData.2.2 hcapUpper
    · intro q hq
      exact node.deep.lower_mem_cap_isSweepEndpoint
        hcapSub hcapData.2.2 hcapUpper
        (Finset.mem_inter.mp hq).1 (Finset.mem_inter.mp hq).2
  exact ⟨hsupport,
    cupProfile configuration.cup₁ configuration.cup₁_mem,
    cupProfile configuration.cup₂ configuration.cup₂_mem,
    cupProfile configuration.cup₃ configuration.cup₃_mem,
    capProfile configuration.cap configuration.cap_mem⟩

/-- Every nontrivial decomposition tree exposes its root split. -/
theorem DecompositionTree.exists_rootSplit_of_two_le_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (tree : DecompositionTree χ support) (hcard : 2 ≤ support.card) :
    ∃ node : DecompositionSplit χ,
      tree.splitAtPath [] = some node ∧
        support = node.lower ∪ node.upper := by
  cases tree with
  | singleton i => simp at hcard
  | split lowerTree upperTree deep =>
      exact ⟨⟨_, _, deep⟩, rfl, rfl⟩

/-- The explicit tree package exposes an actual root split with the aggregate
four-witness profile. -/
theorem ThreeCupRegenerationTree578.exists_rootProfile
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (configurationTree : ThreeCupRegenerationTree578 χ support) :
    ∃ node : DecompositionSplit χ,
      configurationTree.tree.splitAtPath [] = some node ∧
        ThreeCupRegenerationRootProfile578
          configurationTree.configuration node := by
  obtain ⟨node, hlookup, hsupportEq⟩ :=
    configurationTree.tree.exists_rootSplit_of_two_le_card
      (by rw [configurationTree.configuration.support_card]; omega)
  have hsupport : support ⊆ node.lower ∪ node.upper := by
    rw [hsupportEq]
  exact ⟨node, hlookup,
    configurationTree.configuration.rootProfile node hsupport⟩

/-- Restrict a packing and its regenerated cap to the union of the three cups,
discarding the three external caps that were needed only to obtain the global
packing. -/
theorem ThreeDisjointCupCapFourPacking578.toRegenerationConfiguration
    {n : ℕ} {χ : TripleColoring n} {reservoir : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ reservoir)
    {regenerated : Finset (Fin n)}
    (hregenerated : regenerated ∈ capWitnesses χ reservoir 4)
    (hsub : regenerated ⊆ packing.cup₁ ∪ packing.cup₂ ∪ packing.cup₃) :
    Nonempty (ThreeCupRegenerationConfiguration578 χ
      (packing.cup₁ ∪ packing.cup₂ ∪ packing.cup₃)) := by
  have hcup₁Data := mem_capWitnesses.mp packing.cup₁_mem
  have hcup₂Data := mem_capWitnesses.mp packing.cup₂_mem
  have hcup₃Data := mem_capWitnesses.mp packing.cup₃_mem
  have hregeneratedData := mem_capWitnesses.mp hregenerated
  exact ⟨{
    cup₁ := packing.cup₁
    cup₂ := packing.cup₂
    cup₃ := packing.cup₃
    cap := regenerated
    cup₁_mem := mem_capWitnesses.mpr
      ⟨Finset.subset_union_left.trans Finset.subset_union_left,
        hcup₁Data.2⟩
    cup₂_mem := mem_capWitnesses.mpr
      ⟨Finset.subset_union_right.trans Finset.subset_union_left,
        hcup₂Data.2⟩
    cup₃_mem := mem_capWitnesses.mpr
      ⟨Finset.subset_union_right, hcup₃Data.2⟩
    cap_mem := mem_capWitnesses.mpr ⟨hsub, hregeneratedData.2⟩
    cup₁_cup₂ := packing.cup₁_cup₂
    cup₁_cup₃ := packing.cup₁_cup₃
    cup₂_cup₃ := packing.cup₂_cup₃
    support_eq := rfl
  }⟩

theorem SevenWitnessRegenerationPacking578.toRegenerationConfiguration
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ support) :
    Nonempty (ThreeCupRegenerationConfiguration578 χ
      state.packing.cupSupport) := by
  simpa [ThreeDisjointCupCapFourPacking578.cupSupport] using
    state.packing.toRegenerationConfiguration
      state.regenerated_mem state.regenerated_sub

theorem SevenWitnessRegenerationPacking578.incidence
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ support) :
    TwoTwoZeroCupIncidence578 state.regenerated
        state.packing.cup₁ state.packing.cup₂ state.packing.cup₃ ∨
      TwoOneOneCupIncidence578 state.regenerated
        state.packing.cup₁ state.packing.cup₂ state.packing.cup₃ := by
  have hcup₁Data := mem_capWitnesses.mp state.packing.cup₁_mem
  have hcup₂Data := mem_capWitnesses.mp state.packing.cup₂_mem
  have hcup₃Data := mem_capWitnesses.mp state.packing.cup₃_mem
  have hcapData := mem_capWitnesses.mp state.regenerated_mem
  apply twoTwoZero_or_twoOneOne_of_card_eq_four hcapData.2.1
    state.packing.cup₁_cup₂ state.packing.cup₁_cup₃
    state.packing.cup₂_cup₃ state.regenerated_sub
  · exact inter_card_le_two_of_cup_cap
      (isCapSet_dual_iff.mp hcup₁Data.2.2) hcapData.2.2
  · exact inter_card_le_two_of_cup_cap
      (isCapSet_dual_iff.mp hcup₂Data.2.2) hcapData.2.2
  · exact inter_card_le_two_of_cup_cap
      (isCapSet_dual_iff.mp hcup₃Data.2.2) hcapData.2.2

/-- The regenerated cap is disjoint from the whole external cap support, not
merely from one external cap.  This is the first global fact absent from the
minimal local counterexample. -/
theorem SevenWitnessRegenerationPacking578.regenerated_capSupport
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ support) :
    Disjoint state.regenerated state.packing.capSupport := by
  exact state.packing.colors_disjoint.mono state.regenerated_sub
    Finset.Subset.rfl

/-- The regenerated cap and the three external caps form a four-cap packing.
This exact global resource is absent from every twelve-vertex local model. -/
theorem SevenWitnessRegenerationPacking578.fourCaps_pairwise
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ support) :
    ([state.regenerated, state.packing.cap₁, state.packing.cap₂,
      state.packing.cap₃] : List (Finset (Fin n))).Pairwise Disjoint := by
  have hreg : Disjoint state.regenerated state.packing.cap₁ ∧
      Disjoint state.regenerated state.packing.cap₂ ∧
      Disjoint state.regenerated state.packing.cap₃ := by
    simpa [ThreeDisjointCupCapFourPacking578.capSupport] using
      state.regenerated_capSupport
  simpa using ⟨hreg,
    ⟨⟨state.packing.cap₁_cap₂, state.packing.cap₁_cap₃⟩,
      state.packing.cap₂_cap₃⟩⟩

/-- Repackage the exact singleton-root gate without discarding the three
external caps. -/
theorem exists_sevenWitnessRegenerationPacking_of_colorDualLower_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    Nonempty (SevenWitnessRegenerationPacking578 χ reservoir) := by
  obtain ⟨packing, regenerated, hregenerated, hregeneratedSub, _⟩ :=
    exists_dualPackingRegeneration_of_colorDualLower_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong
  exact ⟨{
    packing := packing
    regenerated := regenerated
    regenerated_mem := hregenerated
    regenerated_sub := hregeneratedSub
  }⟩

/-- The exact 32-vertex singleton-root gate produces an explicit decomposable
12-vertex three-cup regeneration configuration. -/
theorem exists_threeCupRegenerationTree_of_colorDualLower_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ∃ support : Finset (Fin n),
      support ⊆ reservoir ∧ support.card = 12 ∧
        Nonempty (ThreeCupRegenerationTree578 χ support) := by
  obtain ⟨packing, regenerated, hregenerated, hregeneratedSub, _⟩ :=
    exists_dualPackingRegeneration_of_colorDualLower_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong
  let support := packing.cup₁ ∪ packing.cup₂ ∪ packing.cup₃
  have hcup₁Data := mem_capWitnesses.mp packing.cup₁_mem
  have hcup₂Data := mem_capWitnesses.mp packing.cup₂_mem
  have hcup₃Data := mem_capWitnesses.mp packing.cup₃_mem
  have hsupportSub : support ⊆ reservoir :=
    Finset.union_subset (Finset.union_subset hcup₁Data.1 hcup₂Data.1)
      hcup₃Data.1
  have hcup₁₂Cup₃ : Disjoint (packing.cup₁ ∪ packing.cup₂) packing.cup₃ :=
    Finset.disjoint_union_left.mpr
      ⟨packing.cup₁_cup₃, packing.cup₂_cup₃⟩
  have hsupportCard : support.card = 12 := by
    rw [Finset.card_union_of_disjoint hcup₁₂Cup₃,
      Finset.card_union_of_disjoint packing.cup₁_cup₂,
      hcup₁Data.2.1, hcup₂Data.2.1, hcup₃Data.2.1]
  have hsupportDecomposable : IsDecomposableOn χ support :=
    hreservoir.subset hsupportSub (Finset.card_pos.mp (by omega))
  obtain ⟨configuration⟩ :=
    packing.toRegenerationConfiguration hregenerated hregeneratedSub
  obtain ⟨tree⟩ := DecompositionTree.exists_of_isDecomposableOn
    hsupportDecomposable
  exact ⟨support, hsupportSub, hsupportCard, ⟨configuration, tree⟩⟩

end ErdosSzekeres

end
