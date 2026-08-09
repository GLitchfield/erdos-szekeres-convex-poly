module

public import ErdosSzekeres.StructuralChargingNextState578Capacity

@[expose] public section

/-!
# Distinct private caps from a minimum terminal-tail transversal

This module sharpens the minimum-transversal invariant.  A cap private to a
selected tail meets the transversal in exactly that tail, so choosing one
private cap per selected tail gives an injection into the family of residual
four-caps.
-/

namespace ErdosSzekeres

namespace DecompositionTree

/-- Every four-cap fails one of the hypotheses of the lower-sibling-bucket
capacity theorem: either some cap vertex has no such bucket, or two distinct
cap vertices collide in one bucket. -/
theorem IsCapSet.exists_uncovered_or_two_in_lowerSiblingBucket_of_card_eq_four
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (tree : DecompositionTree χ support) (path : List Bool)
    (hcap : IsCapSet χ cap) (hcard : cap.card = 4) :
    (∃ x ∈ cap, ¬∃ bucket,
      bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧ x ∈ bucket) ∨
    (∃ bucket, bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧
      ∃ x ∈ cap, ∃ y ∈ cap,
        x ≠ y ∧ x ∈ bucket ∧ y ∈ bucket) := by
  by_cases hcovered : ∀ x ∈ cap, ∃ bucket,
      bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧ x ∈ bucket
  · right
    by_contra hcollision
    have hfiber : ∀ bucket ∈ tree.lowerSiblingSupportsAlongPath path,
        ∀ {x y}, x ∈ cap → y ∈ cap →
          x ∈ bucket → y ∈ bucket → x = y := by
      intro bucket hbucket x y hxCap hyCap hxBucket hyBucket
      by_contra hxy
      exact hcollision ⟨bucket, hbucket, x, hxCap, y, hyCap,
        hxy, hxBucket, hyBucket⟩
    have hsmall := IsCapSet.card_le_three_of_lowerSiblingBucket_fibers
      tree path hcap hcovered hfiber
    omega
  · left
    push Not at hcovered
    obtain ⟨x, hxCap, hxUncovered⟩ := hcovered
    exact ⟨x, hxCap, by
      rintro ⟨bucket, hbucket, hxBucket⟩
      exact hxUncovered bucket hbucket hxBucket⟩

end DecompositionTree

/-- In any four-cap that is not wholly contained in the lower child of a deep
split, both sweep-interior vertices lie in the upper child.  Consequently the
lower child can contain only the two sweep endpoints. -/
theorem capFour_deepSplit_lower_subset_endpoints
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cap : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hcap : cap ∈ capWitnesses χ (lower ∪ upper) 4)
    (hnotLower : ¬cap ⊆ lower) :
    let c := cap.orderEmbOfFin (mem_capWitnesses.mp hcap).2.1
    c 1 ∈ upper ∧ c 2 ∈ upper ∧ cap ∩ lower ⊆ {c 0, c 3} := by
  let hcapCard := (mem_capWitnesses.mp hcap).2.1
  let c := cap.orderEmbOfFin hcapCard
  change c 1 ∈ upper ∧ c 2 ∈ upper ∧ cap ∩ lower ⊆ {c 0, c 3}
  have hcMem (i : Fin 4) : c i ∈ cap :=
    cap.orderEmbOfFin_mem hcapCard i
  have hcUnion (i : Fin 4) : c i ∈ lower ∪ upper :=
    (mem_capWitnesses.mp hcap).1 (hcMem i)
  have hdisjoint : ∀ ⦃x⦄, x ∈ lower → x ∈ upper → False :=
    Finset.disjoint_left.mp hsplit.disjoint
  have hcapSet : IsCapSet χ cap := (mem_capWitnesses.mp hcap).2.2
  have crossing_middle_lower_false
      {i j k : Fin n} (hij : i < j) (hjk : j < k)
      (hiCap : i ∈ cap) (hjCap : j ∈ cap) (hkCap : k ∈ cap)
      (hiUnion : i ∈ lower ∪ upper) (hjUnion : j ∈ lower ∪ upper)
      (hkUnion : k ∈ lower ∪ upper) (hjLower : j ∈ lower)
      (hnotAllLower : ¬(i ∈ lower ∧ j ∈ lower ∧ k ∈ lower)) : False := by
    have hnotAllUpper : ¬(i ∈ upper ∧ j ∈ upper ∧ k ∈ upper) := by
      rintro ⟨_, hjUpper, _⟩
      exact hdisjoint hjLower hjUpper
    have hcross := hsplit.crossing ⟨i, j, k, hij, hjk⟩
      hiUnion hjUnion hkUnion hnotAllLower hnotAllUpper
    rw [if_pos hjLower] at hcross
    have hright := hcapSet ⟨i, j, k, hij, hjk⟩ hiCap hjCap hkCap
    exact Turn.noConfusion (hcross.symm.trans hright)
  have all_lower_of_positions
      (h0 : c 0 ∈ lower) (h1 : c 1 ∈ lower)
      (h2 : c 2 ∈ lower) (h3 : c 3 ∈ lower) : cap ⊆ lower := by
    intro x hxCap
    rw [← Finset.image_orderEmbOfFin_univ cap hcapCard] at hxCap
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxCap
    obtain ⟨i, rfl⟩ := hxCap
    fin_cases i <;> assumption
  have hc1Upper : c 1 ∈ upper := by
    rcases Finset.mem_union.mp (hcUnion 1) with hc1Lower | hc1Upper
    · rcases Finset.mem_union.mp (hcUnion 0) with hc0Lower | hc0Upper
      · rcases Finset.mem_union.mp (hcUnion 2) with hc2Lower | hc2Upper
        · rcases Finset.mem_union.mp (hcUnion 3) with hc3Lower | hc3Upper
          · exact False.elim
              (hnotLower (all_lower_of_positions
                hc0Lower hc1Lower hc2Lower hc3Lower))
          · exact False.elim (crossing_middle_lower_false
              (c.strictMono (by decide))
              (c.strictMono (show (1 : Fin 4) < 3 by decide))
              (hcMem 0) (hcMem 1) (hcMem 3)
              (hcUnion 0) (hcUnion 1) (hcUnion 3) hc1Lower
              (fun h ↦ hdisjoint h.2.2 hc3Upper))
        · exact False.elim (crossing_middle_lower_false
            (c.strictMono (by decide)) (c.strictMono (by decide))
            (hcMem 0) (hcMem 1) (hcMem 2)
            (hcUnion 0) (hcUnion 1) (hcUnion 2) hc1Lower
            (fun h ↦ hdisjoint h.2.2 hc2Upper))
      · exact False.elim (crossing_middle_lower_false
          (c.strictMono (by decide)) (c.strictMono (by decide))
          (hcMem 0) (hcMem 1) (hcMem 2)
          (hcUnion 0) (hcUnion 1) (hcUnion 2) hc1Lower
          (fun h ↦ hdisjoint h.1 hc0Upper))
    · exact hc1Upper
  have hc2Upper : c 2 ∈ upper := by
    rcases Finset.mem_union.mp (hcUnion 2) with hc2Lower | hc2Upper
    · rcases Finset.mem_union.mp (hcUnion 3) with hc3Lower | hc3Upper
      · rcases Finset.mem_union.mp (hcUnion 1) with hc1Lower | hc1Upper'
        · rcases Finset.mem_union.mp (hcUnion 0) with hc0Lower | hc0Upper
          · exact False.elim
              (hnotLower (all_lower_of_positions
                hc0Lower hc1Lower hc2Lower hc3Lower))
          · exact False.elim (crossing_middle_lower_false
              (c.strictMono (show (0 : Fin 4) < 2 by decide))
              (c.strictMono (by decide))
              (hcMem 0) (hcMem 2) (hcMem 3)
              (hcUnion 0) (hcUnion 2) (hcUnion 3) hc2Lower
              (fun h ↦ hdisjoint h.1 hc0Upper))
        · exact False.elim (crossing_middle_lower_false
            (c.strictMono (by decide)) (c.strictMono (by decide))
            (hcMem 1) (hcMem 2) (hcMem 3)
            (hcUnion 1) (hcUnion 2) (hcUnion 3) hc2Lower
            (fun h ↦ hdisjoint h.1 hc1Upper'))
      · exact False.elim (crossing_middle_lower_false
          (c.strictMono (by decide)) (c.strictMono (by decide))
          (hcMem 1) (hcMem 2) (hcMem 3)
          (hcUnion 1) (hcUnion 2) (hcUnion 3) hc2Lower
          (fun h ↦ hdisjoint h.2.2 hc3Upper))
    · exact hc2Upper
  refine ⟨hc1Upper, hc2Upper, ?_⟩
  intro x hx
  have hxData := Finset.mem_inter.mp hx
  have hxCap := hxData.1
  have hxLower := hxData.2
  rw [← Finset.image_orderEmbOfFin_univ cap hcapCard] at hxCap
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hxCap
  obtain ⟨i, rfl⟩ := hxCap
  fin_cases i
  · simp [c]
  · exact False.elim (hdisjoint hxLower hc1Upper)
  · exact False.elim (hdisjoint hxLower hc2Upper)
  · simp [c]

/-- The cap selected for each marked vertex is a genuine four-cap disjoint
from the fixed cap and meets the marked set only in its owner. -/
def IsPrivateFourCapAssignment {n : ℕ} (χ : TripleColoring n)
    (support fixed marked : Finset (Fin n))
    (capFor : Fin n → Finset (Fin n)) : Prop :=
  ∀ x ∈ marked,
    capFor x ∈ capWitnesses χ support 4 ∧
    Disjoint fixed (capFor x) ∧
    x ∈ capFor x ∧
    marked ∩ capFor x = {x}

/-- If the owner of a private cap has a lower-directed first exit, then the
whole-cap bucket dichotomy can choose an uncovered vertex different from the
owner.  Otherwise two distinct vertices of the private cap already collide in
one lower-sibling bucket. -/
theorem IsPrivateFourCapAssignment.privateCap_nonowner_uncovered_or_bucketCollision
    {n : ℕ} {χ : TripleColoring n}
    {support terminal marked : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {capFor : Fin n → Finset (Fin n)}
    (hassign : IsPrivateFourCapAssignment χ support terminal marked capFor)
    {x : Fin n} (hxMarked : x ∈ marked)
    (hexit : DecompositionTree.FirstExitAlongPath terminal x tree path false) :
    (∃ y ∈ capFor x, y ≠ x ∧ ¬∃ bucket,
      bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧ y ∈ bucket) ∨
    (∃ bucket, bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧
      ∃ y ∈ capFor x, ∃ z ∈ capFor x,
        y ≠ z ∧ y ∈ bucket ∧ z ∈ bucket) := by
  have hcapWitness := (hassign x hxMarked).1
  rcases DecompositionTree.IsCapSet.exists_uncovered_or_two_in_lowerSiblingBucket_of_card_eq_four
        tree path (mem_capWitnesses.mp hcapWitness).2.2
        (mem_capWitnesses.mp hcapWitness).2.1 with
    huncovered | hcollision
  · left
    obtain ⟨y, hyCap, hyUncovered⟩ := huncovered
    refine ⟨y, hyCap, ?_, hyUncovered⟩
    intro hyx
    subst y
    obtain ⟨bucket, hbucket, hxBucket⟩ :=
      hexit.mem_lowerSiblingSupportsAlongPath rfl
    exact hyUncovered ⟨bucket, hbucket, hxBucket⟩
  · exact Or.inr hcollision

/-- Choosing one private witness for each marked vertex produces an injective
assignment.  Its finite image therefore has exactly as many distinct caps as
there are marked vertices. -/
theorem exists_card_preserving_privateFourCapAssignment
    {n : ℕ} {χ : TripleColoring n}
    {support fixed marked : Finset (Fin n)}
    (hprivate : ∀ x ∈ marked, ∃ secondary,
      secondary ∈ capWitnesses χ support 4 ∧
      Disjoint fixed secondary ∧ x ∈ secondary ∧
      Disjoint (marked.erase x) secondary) :
    ∃ capFor : Fin n → Finset (Fin n),
      IsPrivateFourCapAssignment χ support fixed marked capFor ∧
      Set.InjOn capFor (marked : Set (Fin n)) ∧
      (marked.image capFor).card = marked.card := by
  classical
  let capFor : Fin n → Finset (Fin n) := fun x ↦
    if hx : x ∈ marked then Classical.choose (hprivate x hx) else ∅
  have hcapFor (x : Fin n) (hxMarked : x ∈ marked) :
      capFor x ∈ capWitnesses χ support 4 ∧
      Disjoint fixed (capFor x) ∧ x ∈ capFor x ∧
      Disjoint (marked.erase x) (capFor x) := by
    simpa [capFor, hxMarked] using
      (Classical.choose_spec (hprivate x hxMarked))
  have hassignment :
      IsPrivateFourCapAssignment χ support fixed marked capFor := by
    intro x hxMarked
    obtain ⟨hcap, hfixed, hxCap, hprivateCap⟩ := hcapFor x hxMarked
    exact ⟨hcap, hfixed, hxCap,
      privateCap_inter_transversal_eq_singleton
        hxMarked hxCap hprivateCap⟩
  have hinjective : Set.InjOn capFor (marked : Set (Fin n)) := by
    intro x hxMarked y hyMarked hcaps
    have hxData := hassignment x hxMarked
    have hyData := hassignment y hyMarked
    apply Finset.singleton_injective
    calc
      {x} = marked ∩ capFor x := hxData.2.2.2.symm
      _ = marked ∩ capFor y := congrArg (marked ∩ ·) hcaps
      _ = {y} := hyData.2.2.2
  exact ⟨capFor, hassignment, hinjective,
    Finset.card_image_of_injOn hinjective⟩

/-- The routed six-tail invariant supplies at least six distinct residual
four-caps, with one cap owned by each routed selected tail. -/
theorem HasSixPrivateRoutedTailTransversal.exists_six_distinct_privateCaps
    {n : ℕ} {χ : TripleColoring n}
    {support terminal tails : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {node : DecompositionSplit χ}
    (h : HasSixPrivateRoutedTailTransversal χ support terminal tails
      tree path node) :
    ∃ transversal, ∃ capFor : Fin n → Finset (Fin n),
      transversal ⊆ tails ∧
      HitsEveryFourCapDisjointFrom χ support terminal transversal ∧
      IsPrivateFourCapAssignment χ support terminal transversal capFor ∧
      (∀ x ∈ transversal,
        IsInternalOrLowerFirstExit terminal x tree path node) ∧
      Set.InjOn capFor (transversal : Set (Fin n)) ∧
      6 ≤ (transversal.image capFor).card := by
  obtain ⟨transversal, htransversalTails, hcard, hhits, hprivate, hroutes⟩ := h
  obtain ⟨capFor, hassignment, hinjective, himageCard⟩ :=
    exists_card_preserving_privateFourCapAssignment hprivate
  exact ⟨transversal, capFor, htransversalTails, hhits, hassignment,
    hroutes, hinjective, by omega⟩

end ErdosSzekeres

end
