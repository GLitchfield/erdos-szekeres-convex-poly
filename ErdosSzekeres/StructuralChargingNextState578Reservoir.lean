module

public import ErdosSzekeres.StructuralChargingNextState578
public import ErdosSzekeres.StructuralChargingTreeAllocation

@[expose] public section

/-!
# Dense cap transversals at the `(5,7,8)` reservoir

The first singleton-lower tail has a 32-vertex upper reservoir in which every
23-vertex restriction contains a four-cap.  This file records the
route-independent consequence: any set meeting every such cap has at least
ten vertices.  It also packages the unique lowest decomposition-tree address
of each cap.  No upper bound on a transversal or closure of the singleton gate
is claimed.
-/

namespace ErdosSzekeres

/-- A cap-witness transversal is an actual subset of the support meeting every
cap witness of the specified cardinality. -/
def IsCapWitnessTransversal {n : ℕ} (χ : TripleColoring n)
    (support transversal : Finset (Fin n)) (a : ℕ) : Prop :=
  transversal ⊆ support ∧
    ∀ cap ∈ capWitnesses χ support a, ¬Disjoint cap transversal

/-- If deleting `deleteBudget` vertices from a support of size
`reservoir + deleteBudget` always leaves a prescribed cap in every
`reservoir`-vertex restriction, then no transversal of those caps fits in the
deletion budget. -/
theorem capWitnessTransversal_card_gt_deleteBudget
    {n a reservoir deleteBudget : ℕ} {χ : TripleColoring n}
    {support transversal : Finset (Fin n)}
    (hcard : support.card = reservoir + deleteBudget)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = reservoir → ContainsCapSet χ subset a)
    (htransversal : IsCapWitnessTransversal χ support transversal a) :
    deleteBudget < transversal.card := by
  by_contra hsmall
  have htransversalCard : transversal.card ≤ deleteBudget := by omega
  let rest := support \ transversal
  have hrestCard : reservoir ≤ rest.card := by
    rw [Finset.card_sdiff_of_subset htransversal.1, hcard]
    omega
  obtain ⟨subset, hsubsetRest, hsubsetCard⟩ :=
    Finset.exists_subset_card_eq hrestCard
  have hsubsetSupport : subset ⊆ support :=
    hsubsetRest.trans Finset.sdiff_subset
  obtain ⟨cap, hcapSub, hcapCard, hcapSet⟩ :=
    hdense subset hsubsetSupport hsubsetCard
  have hcapMem : cap ∈ capWitnesses χ support a :=
    mem_capWitnesses.mpr
      ⟨hcapSub.trans hsubsetSupport, hcapCard, hcapSet⟩
  have hdisjoint : Disjoint cap transversal := by
    rw [Finset.disjoint_left]
    intro q hqCap hqTransversal
    have hqRest := hsubsetRest (hcapSub hqCap)
    exact (Finset.mem_sdiff.mp hqRest).2 hqTransversal
  exact htransversal.2 cap hcapMem hdisjoint

/-- At the exact `(5,7,8)` lower-tail reservoir, every transversal of the
upper four-cap family contains at least ten vertices. -/
theorem ten_le_capWitnessTransversal_at_578
    {n : ℕ} {χ : TripleColoring n}
    {upper transversal : Finset (Fin n)}
    (hupperCard : upper.card = 32)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ upper →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (htransversal : IsCapWitnessTransversal χ upper transversal 4) :
    10 ≤ transversal.card := by
  have hgt := capWitnessTransversal_card_gt_deleteBudget
    (reservoir := 23) (deleteBudget := 9)
    (by omega) hdense htransversal
  omega

/-- The compiled dense-reservoir theorem supplies the hypotheses of the exact
ten-vertex transversal lower bound. -/
theorem ten_le_fourCapTransversal_of_open_singleton_lower_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper transversal : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hupperCard : upper.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8)
    (htransversal : IsCapWitnessTransversal χ upper transversal 4) :
    10 ≤ transversal.card := by
  have hdense :=
    (dense_straddling_cap_reservoir_at_578
      hupper hroot hnoCap hnoCup hnoStrong).1
  exact ten_le_capWitnessTransversal_at_578 hupperCard hdense htransversal

/-- In an open singleton-lower state, no upper four-cap can be weakly before
another.  Both spans cover the singleton root cut, while weak separation
would place the first span entirely before the second. -/
theorem fourCapWitnesses_not_weaklyBefore_of_open_singleton_lower
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper earlier later : Finset (Fin n)}
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hearlier : earlier ∈ capWitnesses χ upper 4)
    (hlater : later ∈ capWitnesses χ upper 4) :
    ¬FinsetWeaklyBefore earlier later := by
  intro hbefore
  have hearlierData := mem_capWitnesses.mp hearlier
  have hlaterData := mem_capWitnesses.mp hlater
  exact hnoCap
    (hroot.containsCapSet_five_of_separated_upper_four_caps
      hearlierData.1 hlaterData.1 hearlierData.2.1 hlaterData.2.1
      hearlierData.2.2 hlaterData.2.2 hbefore)

/-- Consequently the ordered-cap hypothesis used by the existing local tree
capacity theorem is vacuous beyond one cap in an open singleton-lower state.
Any useful tree recurrence here must retain a different order invariant. -/
theorem ordered_fourCapWitness_family_card_le_one_of_open_singleton_lower
    {n m : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)} (caps : Fin m → Finset (Fin n))
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hcaps : ∀ i, caps i ∈ capWitnesses χ upper 4)
    (hordered : ∀ {i j}, i < j → FinsetWeaklyBefore (caps i) (caps j)) :
    m ≤ 1 := by
  by_contra hlarge
  have hm : 2 ≤ m := by omega
  let first : Fin m := ⟨0, by omega⟩
  let second : Fin m := ⟨1, by omega⟩
  have hlt : first < second := by simp [first, second]
  exact
    (fourCapWitnesses_not_weaklyBefore_of_open_singleton_lower
      hroot hnoCap (hcaps first) (hcaps second)) (hordered hlt)

/-- The tempting assertion that every open singleton-lower reservoir has a
nine-vertex transversal.  It is named here only so that its logical strength
can be checked exactly. -/
def NineCapTransversalGate578 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {upper : Finset (Fin n)},
    IsDecomposableOn χ upper →
    HasDeepBelowSplit χ {q} upper →
    upper.card = 32 →
    ¬ContainsCapSet χ ({q} ∪ upper) 5 →
    ¬ContainsCupSet χ ({q} ∪ upper) 7 →
    ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8 →
    ∃ transversal,
      IsCapWitnessTransversal χ upper transversal 4 ∧
      transversal.card ≤ 9

/-- A universal nine-vertex-transversal assertion is not a weaker bridge to
the singleton-lower gate: under exactly the open-root hypotheses, it is
logically equivalent to the full gate.  The forward implication contradicts
the compiled ten-vertex lower bound; the reverse implication is vacuous once
the gate has excluded every such reservoir. -/
theorem nineCapTransversalGate578_iff_singletonLowerCriticalGate578 :
    NineCapTransversalGate578 ↔ SingletonLowerCriticalGate578 := by
  constructor
  · intro htransversal n χ q upper hupper hroot hupperCard
      hnoCap hnoCup hnoStrong
    obtain ⟨transversal, htransversal, hcard⟩ :=
      htransversal hupper hroot hupperCard hnoCap hnoCup hnoStrong
    have hten :=
      ten_le_fourCapTransversal_of_open_singleton_lower_at_578
        hupper hroot hupperCard hnoCap hnoCup hnoStrong htransversal
    omega
  · intro hgate n χ q upper hupper hroot hupperCard hnoCap hnoCup hnoStrong
    exact (hgate hupper hroot hupperCard hnoCap hnoCup hnoStrong).elim

/-- A cap together with its actual lowest separating-node address in one
fixed explicit decomposition tree. -/
structure TreeOwnedCapWitness {n : ℕ} (χ : TripleColoring n)
    {support : Finset (Fin n)} (tree : DecompositionTree χ support)
    (a : ℕ) where
  cap : Finset (Fin n)
  cap_mem : cap ∈ capWitnesses χ support a
  path : List Bool
  node : DecompositionSplit χ
  allocated : DecompositionTree.IsLowestSeparatingPath cap tree path
  lookup : tree.splitAtPath path = some node

/-- Every cap of cardinality at least two receives an actual lowest tree
address. -/
theorem exists_treeOwnedCapWitness_of_mem
    {n a : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (tree : DecompositionTree χ support) (ha : 2 ≤ a)
    (hcap : cap ∈ capWitnesses χ support a) :
    ∃ owned : TreeOwnedCapWitness χ tree a, owned.cap = cap := by
  have hsub : cap ⊆ support := (mem_capWitnesses.mp hcap).1
  have hcard : 2 ≤ cap.card := by
    rw [(mem_capWitnesses.mp hcap).2.1]
    exact ha
  obtain ⟨node, hlookup, _, _, _⟩ :=
    tree.lowestSeparatingPath_spec hsub hcard
  exact ⟨{
    cap := cap
    cap_mem := hcap
    path := tree.lowestSeparatingPath hsub hcard
    node := node
    allocated := tree.lowestSeparatingPath_isLowest hsub hcard
    lookup := hlookup
  }, rfl⟩

/-- Stable cap identity prevents the same cap from receiving two addresses in
the same explicit tree. -/
theorem TreeOwnedCapWitness.same_cap_same_path
    {n a : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {tree : DecompositionTree χ support}
    (ha : 2 ≤ a)
    (first second : TreeOwnedCapWitness χ tree a)
    (hcap : first.cap = second.cap) :
    first.path = second.path := by
  have hsecondAllocated :
      DecompositionTree.IsLowestSeparatingPath first.cap tree second.path := by
    simpa [hcap] using second.allocated
  have hsub : first.cap ⊆ support :=
    (mem_capWitnesses.mp first.cap_mem).1
  have hcard : 2 ≤ first.cap.card := by
    rw [(mem_capWitnesses.mp first.cap_mem).2.1]
    exact ha
  exact first.allocated.unique hsecondAllocated hsub hcard

end ErdosSzekeres

end
