module

public import ErdosSzekeres.HMPTSpikeOrderDefs
public import ErdosSzekeres.SukAdjacentSupportProducer

@[expose] public section

/-!
# HMPT vertical-chain profiles

This file defines the data produced in the second finite layer of the
Holmsen--Mojarrad--Pach--Tardos argument.  It records anchored subchains of an
actual maximum vertical chain, their exact binomial bound, and the raw geometry
of two adjacent spike pools.  No convexity conclusion for the adjacent union is
a field.
-/

namespace ErdosSzekeres

noncomputable section

/-- Regard a finite set of points in a subtype as the same finite point set in
the ambient plane. -/
def hmptChainPoints {s : Finset (Point 2)}
    (chain : Finset (↥s)) : Finset (Point 2) :=
  chain.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem hmptChainPoints_card
    {s : Finset (Point 2)} (chain : Finset (↥s)) :
    (hmptChainPoints chain).card = chain.card := by
  simp [hmptChainPoints]

theorem hmptChainPoints_subset
    {s : Finset (Point 2)} (chain : Finset (↥s)) :
    hmptChainPoints chain ⊆ s := by
  intro p hp
  rcases Finset.mem_map.mp hp with ⟨q, _, rfl⟩
  exact q.property

/-- The source color on a triple in a vertical chain.  A negative turn is the
right color and a positive turn is the left color. -/
def hmptVerticalTripleColor {s : Finset (Point 2)}
    (p q r : ↥s) : Turn :=
  if orientation p.1 q.1 r.1 < 0 then Turn.right else Turn.left

/-- The four-point transitivity law for the source coloring, stated in the
strict HMPT vertical direction. -/
def HMPTVerticalTransitiveColoring
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (color : ↥s → ↥s → ↥s → Turn) : Prop :=
  ∀ p q r t : ↥s,
    HMPTSpikeVerticalLT outerLeft outerRight p.1 q.1 →
    HMPTSpikeVerticalLT outerLeft outerRight q.1 r.1 →
    HMPTSpikeVerticalLT outerLeft outerRight r.1 t.1 →
    ∀ c : Turn, color p q r = c → color q r t = c →
      color p q t = c ∧ color p r t = c

/-- A point subset of an ambient vertical chain whose extension by the named
anchor is in convex position. -/
def HMPTAnchoredVerticalSubchain
    {s : Finset (Point 2)} (anchor : Point 2)
    (verticalChain selected : Finset (↥s)) : Prop :=
  selected ⊆ verticalChain ∧
    InConvexPosition (insert anchor (hmptChainPoints selected))

/-- A cardinality-maximum anchored subchain of an ambient vertical chain. -/
def HMPTMaximumAnchoredVerticalSubchain
    {s : Finset (Point 2)} (anchor : Point 2)
    (verticalChain selected : Finset (↥s)) : Prop :=
  HMPTAnchoredVerticalSubchain anchor verticalChain selected ∧
    ∀ other : Finset (↥s),
      HMPTAnchoredVerticalSubchain anchor verticalChain other →
        other.card ≤ selected.card

/-- The complete local vertical-chain profile used in the HMPT recurrence.
The left and right anchors occur in the types of their maximum subchains. -/
structure HMPTVerticalProfile
    (outerLeft rightAnchor leftAnchor outerRight : Point 2)
    (s : Finset (Point 2)) where
  verticalChain : Finset (↥s)
  horizontalChain : Finset (↥s)
  verticalMaximum : HMPTMaximumChain
    (fun p q : ↥s ↦ HMPTSpikeVerticalLE outerLeft outerRight p.1 q.1)
    verticalChain
  horizontalMaximum : HMPTMaximumChain
    (fun p q : ↥s ↦ HMPTSpikeHorizontalLE outerLeft outerRight p.1 q.1)
    horizontalChain
  poolCard_le_product :
    s.card ≤ verticalChain.card * horizontalChain.card
  leftChain : Finset (↥s)
  rightChain : Finset (↥s)
  leftMaximum :
    HMPTMaximumAnchoredVerticalSubchain outerLeft verticalChain leftChain
  rightMaximum :
    HMPTMaximumAnchoredVerticalSubchain outerRight verticalChain rightChain
  verticalCard_le_choose :
    verticalChain.card ≤
      Nat.choose (leftChain.card + rightChain.card - 2) (leftChain.card - 1)

/-- Raw geometry of two consecutive spike pools.  The first profile uses
`x0`/`x3` as its outer anchors and the second uses `x1`/`x4`; consequently the
chains glued by H2 are anchored at the distinct points `x3` and `x1`. -/
structure HMPTAdjacentSpikeGeometry
    (x0 x1 x2 x3 x4 : Point 2)
    (leftPool rightPool : Finset (Point 2)) : Prop where
  anchorsCap : SukFiveCapAnchors x0 x1 x2 x3 x4
  disjoint : Disjoint leftPool rightPool
  generalPosition : InGeneralPosition
    (insert x0 (insert x1
      (insert x2 (insert x3 (insert x4 (leftPool ∪ rightPool))))))
  leftRegion : ∀ ⦃p⦄, p ∈ leftPool →
    p ∈ SukSupportRegion x0 x1 x2 x3
  rightRegion : ∀ ⦃p⦄, p ∈ rightPool →
    p ∈ SukSupportRegion x1 x2 x3 x4

end

end ErdosSzekeres

end
