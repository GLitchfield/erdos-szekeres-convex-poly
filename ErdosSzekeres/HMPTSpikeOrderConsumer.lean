module

public import ErdosSzekeres.FiniteDilworth
public import ErdosSzekeres.HMPTSpikeOrderDefs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-!
# The finite HMPT spike-order consumer

This file constructs actual maximum chains in the two HMPT spike orders and
derives the exact product bound for one finite spike pool.  All geometry is
encapsulated by the frozen `HMPTSpikeOrderPair` interface.
-/

namespace ErdosSzekeres

noncomputable section

@[reducible] private def HMPTSpikeOrderPair.verticalPartialOrder
    {outerLeft outerRight : Point 2} {s : Finset (Point 2)}
    (h : HMPTSpikeOrderPair outerLeft outerRight s) :
    PartialOrder (↥s) where
  le p q := HMPTSpikeVerticalLE outerLeft outerRight p q
  lt p q :=
    HMPTSpikeVerticalLE outerLeft outerRight p q ∧
      ¬ HMPTSpikeVerticalLE outerLeft outerRight q p
  le_refl := h.vertical_refl
  le_trans := h.vertical_trans
  le_antisymm := h.vertical_antisymm
  lt_iff_le_not_ge _ _ := Iff.rfl

private theorem exists_hmptMaximumChain
    {s : Finset (Point 2)} (rel : ↥s → ↥s → Prop) :
    ∃ chain : Finset (↥s), HMPTMaximumChain rel chain := by
  classical
  let candidates : Finset (Finset (↥s)) :=
    Finset.univ.powerset.filter fun chain ↦
      IsChain rel (chain : Set (↥s))
  have hempty : (∅ : Finset (↥s)) ∈ candidates := by
    simp [candidates]
  obtain ⟨chain, hchainMem, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  refine ⟨chain, (Finset.mem_filter.mp hchainMem).2, ?_⟩
  intro other hother
  apply hmax other
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hother⟩
  intro p _
  exact Finset.mem_attach s p

private theorem HMPTSpikeOrderPair.horizontalChain_of_verticalAntichain
    {outerLeft outerRight : Point 2} {s : Finset (Point 2)}
    (h : HMPTSpikeOrderPair outerLeft outerRight s)
    {t : Finset (↥s)}
    (hanti : IsAntichain
      (fun p q : ↥s ↦ HMPTSpikeVerticalLE outerLeft outerRight p q)
      (t : Set (↥s))) :
    IsChain
      (fun p q : ↥s ↦ HMPTSpikeHorizontalLE outerLeft outerRight p q)
      (t : Set (↥s)) := by
  intro p hp q hq hpq
  rcases (h.exclusive_comparability p q hpq).1 with hvertical | hhorizontal
  · rcases hvertical with hpqVertical | hqpVertical
    · exact (hanti hp hq hpq hpqVertical).elim
    · exact (hanti hq hp hpq.symm hqpVertical).elim
  · exact hhorizontal

/-- Equation (3): actual maximum chains in the two HMPT orders control the
cardinality of the whole spike pool. -/
theorem HMPTSpikeOrderPair.exists_maxChains_card_le_product
    {outerLeft outerRight : Point 2} {s : Finset (Point 2)}
    (h : HMPTSpikeOrderPair outerLeft outerRight s) :
    ∃ verticalChain horizontalChain : Finset (↥s),
      HMPTMaximumChain
          (fun p q : ↥s ↦ HMPTSpikeVerticalLE outerLeft outerRight p q)
          verticalChain ∧
        HMPTMaximumChain
          (fun p q : ↥s ↦ HMPTSpikeHorizontalLE outerLeft outerRight p q)
          horizontalChain ∧
        s.card ≤ verticalChain.card * horizontalChain.card := by
  classical
  obtain ⟨verticalChain, hvertical⟩ := exists_hmptMaximumChain
    (fun p q : ↥s ↦ HMPTSpikeVerticalLE outerLeft outerRight p q)
  obtain ⟨horizontalChain, hhorizontal⟩ := exists_hmptMaximumChain
    (fun p q : ↥s ↦ HMPTSpikeHorizontalLE outerLeft outerRight p q)
  refine ⟨verticalChain, horizontalChain, hvertical, hhorizontal, ?_⟩
  by_contra hproduct
  have hcard : verticalChain.card * horizontalChain.card < s.card := by
    omega
  letI : PartialOrder (↥s) := h.verticalPartialOrder
  have hunivCard : (Finset.univ : Finset (↥s)).card = s.card := by
    simp
  obtain ⟨t, -, hlargeChain | hlargeAntichain⟩ :=
    finiteDilworth_chain_or_antichain
      (Finset.univ : Finset (↥s)) verticalChain.card horizontalChain.card
      (by simpa [hunivCard] using hcard)
  · rcases hlargeChain with ⟨hlargeCard, htChain⟩
    change IsChain
      (fun p q : ↥s ↦ HMPTSpikeVerticalLE outerLeft outerRight p q)
      (t : Set (↥s)) at htChain
    have htBound := hvertical.2 t htChain
    omega
  · rcases hlargeAntichain with ⟨hlargeCard, htAntichain⟩
    change IsAntichain
      (fun p q : ↥s ↦ HMPTSpikeVerticalLE outerLeft outerRight p q)
      (t : Set (↥s)) at htAntichain
    have htHorizontal := h.horizontalChain_of_verticalAntichain htAntichain
    have htBound := hhorizontal.2 t htHorizontal
    omega

end

end ErdosSzekeres

end
