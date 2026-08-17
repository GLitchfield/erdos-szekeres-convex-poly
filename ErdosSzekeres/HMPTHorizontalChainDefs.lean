module

public import ErdosSzekeres.HMPTVerticalChainDefs

@[expose] public section

/-!
# HMPT horizontal-chain profiles

This file defines the literal inner/outer triple predicates and the data
produced by the third finite HMPT layer. Whole-chain convexity and every
cross-pool gluing statement remain outside this interface.
-/

namespace ErdosSzekeres

noncomputable section

/-- The source color on a triple in a horizontal chain. Negative orientation
is the inner color, represented by `Turn.right`. -/
def hmptHorizontalTripleColor {s : Finset (Point 2)}
    (p q r : ↥s) : Turn :=
  if orientation p.1 q.1 r.1 < 0 then Turn.right else Turn.left

/-- Four-point transitivity of a triple coloring along the strict HMPT
horizontal order. -/
def HMPTHorizontalTransitiveColoring
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (color : ↥s → ↥s → ↥s → Turn) : Prop :=
  ∀ p q r t : ↥s,
    HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1 →
    HMPTSpikeHorizontalLT outerLeft outerRight q.1 r.1 →
    HMPTSpikeHorizontalLT outerLeft outerRight r.1 t.1 →
    ∀ c : Turn, color p q r = c → color q r t = c →
      color p q t = c ∧ color p r t = c

/-- Literal inner/outer semantics of the two colors on increasing horizontal
triples. -/
def HMPTHorizontalTripleSemantics
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (color : ↥s → ↥s → ↥s → Turn) : Prop :=
  ∀ p q r : ↥s,
    HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1 →
    HMPTSpikeHorizontalLT outerLeft outerRight q.1 r.1 →
      (color p q r = Turn.right ↔
        InConvexPosition {outerLeft, outerRight, p.1, q.1, r.1}) ∧
      (color p q r = Turn.left ↔
        ¬InConvexPosition {outerLeft, outerRight, p.1, q.1, r.1})

/-- The complete local geometric statement required by the H3 finite
recurrence. -/
structure HMPTHorizontalTripleGeometry
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (color : ↥s → ↥s → ↥s → Turn) : Prop where
  transitive :
    HMPTHorizontalTransitiveColoring outerLeft outerRight color
  semantics : HMPTHorizontalTripleSemantics outerLeft outerRight color

/-- A literal inner horizontal subchain of an ambient horizontal chain. The
quantification by three-element finsets makes the predicate permutation
invariant and vacuous for chains of cardinality at most two. -/
def HMPTInnerHorizontalSubchain
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (horizontalChain selected : Finset (↥s)) : Prop :=
  selected ⊆ horizontalChain ∧
    ∀ triple : Finset (↥s), triple ⊆ selected → triple.card = 3 →
      InConvexPosition
        (insert outerLeft (insert outerRight (hmptChainPoints triple)))

/-- A literal outer horizontal subchain of an ambient horizontal chain. -/
def HMPTOuterHorizontalSubchain
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (horizontalChain selected : Finset (↥s)) : Prop :=
  selected ⊆ horizontalChain ∧
    ∀ triple : Finset (↥s), triple ⊆ selected → triple.card = 3 →
      ¬InConvexPosition
        (insert outerLeft (insert outerRight (hmptChainPoints triple)))

/-- A cardinality-maximum literal inner subchain. -/
def HMPTMaximumInnerHorizontalSubchain
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (horizontalChain selected : Finset (↥s)) : Prop :=
  HMPTInnerHorizontalSubchain outerLeft outerRight horizontalChain selected ∧
    ∀ other : Finset (↥s),
      HMPTInnerHorizontalSubchain outerLeft outerRight horizontalChain other →
        other.card ≤ selected.card

/-- A cardinality-maximum literal outer subchain. -/
def HMPTMaximumOuterHorizontalSubchain
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (horizontalChain selected : Finset (↥s)) : Prop :=
  HMPTOuterHorizontalSubchain outerLeft outerRight horizontalChain selected ∧
    ∀ other : Finset (↥s),
      HMPTOuterHorizontalSubchain outerLeft outerRight horizontalChain other →
        other.card ≤ selected.card

/-- The H3 horizontal profile attached to the exact H2 profile and its
unchanged maximum horizontal chain. -/
structure HMPTHorizontalProfile
    (outerLeft rightAnchor leftAnchor outerRight : Point 2)
    (s : Finset (Point 2))
    (verticalProfile : HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s) where
  innerChain : Finset (↥s)
  outerChain : Finset (↥s)
  innerMaximum : HMPTMaximumInnerHorizontalSubchain
    outerLeft outerRight verticalProfile.horizontalChain innerChain
  outerMaximum : HMPTMaximumOuterHorizontalSubchain
    outerLeft outerRight verticalProfile.horizontalChain outerChain
  horizontalCard_le_choose :
    verticalProfile.horizontalChain.card ≤
      Nat.choose (innerChain.card + outerChain.card - 2)
        (innerChain.card - 1)

end

end ErdosSzekeres

end
