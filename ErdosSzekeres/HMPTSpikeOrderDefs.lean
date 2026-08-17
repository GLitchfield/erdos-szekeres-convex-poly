module

public import ErdosSzekeres.SukAdjacentRegions
public import Mathlib.Order.Preorder.Chain

@[expose] public section

/-!
# The two HMPT spike orders

This file defines the vertical and horizontal orders used on one spike pool in
the Holmsen--Mojarrad--Pach--Tardos argument.  It also records the exact local
order-pair interface and the notion of a maximum finite chain consumed by the
finite product theorem.
-/

namespace ErdosSzekeres

noncomputable section

/-- Source-direction vertical strict order: the triangle based at `p` is
contained in the triangle based at `q`. -/
def HMPTSpikeVerticalLT
    (outerLeft outerRight p q : Point 2) : Prop :=
  p ≠ q ∧
    convexHull ℝ (triangle outerLeft outerRight p) ⊆
      convexHull ℝ (triangle outerLeft outerRight q)

/-- Source horizontal strict order: the crossed anchor-to-point segments meet. -/
def HMPTSpikeHorizontalLT
    (outerLeft outerRight p q : Point 2) : Prop :=
  p ≠ q ∧
    Set.Nonempty
      (convexHull ℝ ({outerLeft, q} : Set (Point 2)) ∩
        convexHull ℝ ({outerRight, p} : Set (Point 2)))

/-- Reflexive closure of the source vertical strict order. -/
def HMPTSpikeVerticalLE
    (outerLeft outerRight p q : Point 2) : Prop :=
  p = q ∨ HMPTSpikeVerticalLT outerLeft outerRight p q

/-- Reflexive closure of the source horizontal strict order. -/
def HMPTSpikeHorizontalLE
    (outerLeft outerRight p q : Point 2) : Prop :=
  p = q ∨ HMPTSpikeHorizontalLT outerLeft outerRight p q

/-- Both source relations are partial orders, and distinct pool points are
comparable in exactly one of them. -/
structure HMPTSpikeOrderPair
    (outerLeft outerRight : Point 2) (s : Finset (Point 2)) : Prop where
  vertical_refl : ∀ p : ↥s,
    HMPTSpikeVerticalLE outerLeft outerRight p p
  vertical_antisymm : ∀ p q : ↥s,
    HMPTSpikeVerticalLE outerLeft outerRight p q →
      HMPTSpikeVerticalLE outerLeft outerRight q p → p = q
  vertical_trans : ∀ p q r : ↥s,
    HMPTSpikeVerticalLE outerLeft outerRight p q →
      HMPTSpikeVerticalLE outerLeft outerRight q r →
        HMPTSpikeVerticalLE outerLeft outerRight p r
  horizontal_refl : ∀ p : ↥s,
    HMPTSpikeHorizontalLE outerLeft outerRight p p
  horizontal_antisymm : ∀ p q : ↥s,
    HMPTSpikeHorizontalLE outerLeft outerRight p q →
      HMPTSpikeHorizontalLE outerLeft outerRight q p → p = q
  horizontal_trans : ∀ p q r : ↥s,
    HMPTSpikeHorizontalLE outerLeft outerRight p q →
      HMPTSpikeHorizontalLE outerLeft outerRight q r →
        HMPTSpikeHorizontalLE outerLeft outerRight p r
  exclusive_comparability : ∀ p q : ↥s, p ≠ q →
    (((HMPTSpikeVerticalLE outerLeft outerRight p q ∨
          HMPTSpikeVerticalLE outerLeft outerRight q p) ∨
        (HMPTSpikeHorizontalLE outerLeft outerRight p q ∨
          HMPTSpikeHorizontalLE outerLeft outerRight q p)) ∧
      ¬ ((HMPTSpikeVerticalLE outerLeft outerRight p q ∨
            HMPTSpikeVerticalLE outerLeft outerRight q p) ∧
          (HMPTSpikeHorizontalLE outerLeft outerRight p q ∨
            HMPTSpikeHorizontalLE outerLeft outerRight q p)))

/-- A finite chain whose cardinality dominates every chain for the same relation. -/
def HMPTMaximumChain
    {s : Finset (Point 2)}
    (rel : ↥s → ↥s → Prop) (chain : Finset (↥s)) : Prop :=
  IsChain rel (chain : Set (↥s)) ∧
    ∀ other : Finset (↥s),
      IsChain rel (other : Set (↥s)) → other.card ≤ chain.card

end

end ErdosSzekeres

end
