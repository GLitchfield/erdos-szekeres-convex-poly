module

public import ErdosSzekeres.StructuralChargingCupBlocks45

@[expose] public section

/-!
# Singleton-root separated-cap charge at six

This file isolates the exact root-local cross-gap statement suggested by the
structural-charging interval and cup-block layers.  The existing endpoint
straddling law proves a stronger fact: two separated upper four-caps already
force a parent five-cap.  No generated state-566 certificate is used.
-/

namespace ErdosSzekeres

/-- If a parent has no cap of size `a + 1`, every lower-child vertex lies in
the sweep interval of each upper `a`-cap.  This is the arbitrary-lower-child
form of the common-cut resource; it does not assume the lower child is a
singleton or contiguous in sweep order. -/
theorem HasDeepBelowSplit.every_lower_vertex_straddles_upper_cap_of_no_succ_cap
    {n a : ℕ} {χ : TripleColoring n}
    {lower upper cap : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper) (ha : 0 < a)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) (a + 1))
    (hcap : cap ∈ capWitnesses χ upper a) :
    ∀ q ∈ lower,
      (finsetSweepInterval cap (by
        have hcard := (mem_capWitnesses.mp hcap).2.1
        exact Finset.card_pos.mp (by omega))).StraddlesCut q.val := by
  intro q hqLower
  have hcapData := mem_capWitnesses.mp hcap
  have hcapNonempty : cap.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨⟨x, hxCap, hxq⟩, ⟨y, hyCap, hqy⟩⟩ :=
    h.cap_straddles_lower_of_not_containsCapSet_succ hcapData.1
      hcapData.2.1 hcapData.2.2 hqLower hnoCap
  change (cap.min' hcapNonempty).val < q.val ∧
    q.val ≤ (cap.max' hcapNonempty).val
  constructor
  · exact (Finset.min'_le cap x hxCap).trans_lt hxq
  · exact hqy.le.trans (Finset.le_max' cap y hyCap)

/-- Structural resource at the first non-index-one saturated boundary.

An upper child larger than the classical `(3,6)` threshold contains a
three-cap unless it already contains a parent six-cup. If the parent also has
no four-cap, that three-cap's interval covers every lower-child vertex. No
finite state-466/566 theorem or certificate is used. -/
theorem first_saturated_boundary_has_covering_upper_three_cap
    {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (hχ : IsSweepRealizable χ) (h : HasDeepBelowSplit χ lower upper)
    (hupperLarge : 5 < upper.card)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 6) :
    ∃ cap : {cap // cap ∈ capWitnesses χ upper 3},
      ∀ q ∈ lower,
        (finsetSweepInterval cap.1 (by
          have hcard := (mem_capWitnesses.mp cap.property).2.1
          exact Finset.card_pos.mp (by omega))).StraddlesCut q.val := by
  have hcard : Nat.choose (3 + 6 - 4) (3 - 2) < upper.card := by
    norm_num
    exact hupperLarge
  rcases containsCapSet_or_containsCupSet_of_choose_lt hχ upper
      (a := 3) (u := 6) (by omega) (by omega) hcard with hcap | hcup
  · obtain ⟨cap, hcapSub, hcapCard, hcapSet⟩ := hcap
    have hcapWitness : cap ∈ capWitnesses χ upper 3 :=
      mem_capWitnesses.mpr ⟨hcapSub, hcapCard, hcapSet⟩
    exact ⟨⟨cap, hcapWitness⟩,
      h.every_lower_vertex_straddles_upper_cap_of_no_succ_cap
        (a := 3) (by omega) hnoCap hcapWitness⟩
  · exact (hnoCup
      (FinsetPolygon.ContainsCupSet.mono hcup Finset.subset_union_right)).elim

/-- If a singleton-root parent has no cap of size `a + 1`, then the root is a
common sweep cut for every upper cap of size `a`.

This parameterized form is the common-cut branch of the structural descent;
it is not specific to the first `k = 6` test case. -/
theorem HasDeepBelowSplit.root_straddles_every_upper_cap_of_no_succ_cap
    {n a : ℕ} {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (hroot : HasDeepBelowSplit χ {q} upper) (ha : 0 < a)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) (a + 1))
    (cap : Finset (Fin n)) (hcap : cap ∈ capWitnesses χ upper a) :
    (finsetSweepInterval cap (by
      have hcard := (mem_capWitnesses.mp hcap).2.1
      exact Finset.card_pos.mp (by omega))).StraddlesCut q.val := by
  have hcapData := mem_capWitnesses.mp hcap
  have hcapNonempty : cap.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨⟨x, hxCap, hxq⟩, ⟨y, hyCap, hqy⟩⟩ :=
    hroot.cap_straddles_lower_of_not_containsCapSet_succ hcapData.1
      hcapData.2.1 hcapData.2.2 (q := q) (by simp) hnoCap
  change (cap.min' hcapNonempty).val < q.val ∧
    q.val ≤ (cap.max' hcapNonempty).val
  constructor
  · exact (Finset.min'_le cap x hxCap).trans_lt hxq
  · exact hqy.le.trans (Finset.le_max' cap y hyCap)

/-- Under the same hypotheses, the upper `a`-cap witness family has an
explicit common cut, namely the singleton root's sweep index. -/
theorem HasDeepBelowSplit.exists_common_cut_for_upper_caps_of_no_succ_cap
    {n a : ℕ} {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (hroot : HasDeepBelowSplit χ {q} upper) (ha : 0 < a)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) (a + 1)) :
    ∃ cut : ℕ,
      ∀ (cap : Finset (Fin n)) (hcap : cap ∈ capWitnesses χ upper a),
        (finsetSweepInterval cap (by
          have hcard := (mem_capWitnesses.mp hcap).2.1
          exact Finset.card_pos.mp (by omega))).StraddlesCut cut := by
  exact ⟨q.val, hroot.root_straddles_every_upper_cap_of_no_succ_cap ha hnoCap⟩

/-- Two weakly separated upper four-caps at a singleton deep-below root force
a five-cap in the parent.

Indeed, if no parent five-cap existed, the endpoint transition would make
every upper four-cap strictly straddle the root.  Weak separation makes it
impossible for both witnesses to do so. -/
theorem HasDeepBelowSplit.containsCapSet_five_of_separated_upper_four_caps
    {n : ℕ} {χ : TripleColoring n} {upper earlier later : Finset (Fin n)}
    {q : Fin n} (hroot : HasDeepBelowSplit χ {q} upper)
    (hearlierSub : earlier ⊆ upper) (hlaterSub : later ⊆ upper)
    (hearlierCard : earlier.card = 4) (hlaterCard : later.card = 4)
    (hearlierCap : IsCapSet χ earlier) (hlaterCap : IsCapSet χ later)
    (hbefore : FinsetWeaklyBefore earlier later) :
    ContainsCapSet χ ({q} ∪ upper) 5 := by
  by_contra hnoCap
  have hearlierStraddles := hroot.cap_straddles_lower_of_not_containsCapSet_succ
    hearlierSub hearlierCard hearlierCap (q := q) (by simp) hnoCap
  have hlaterStraddles := hroot.cap_straddles_lower_of_not_containsCapSet_succ
    hlaterSub hlaterCard hlaterCap (q := q) (by simp) hnoCap
  obtain ⟨y, hyEarlier, hqy⟩ := hearlierStraddles.2
  obtain ⟨x, hxLater, hxq⟩ := hlaterStraddles.1
  have hyx : y ≤ x := hbefore y hyEarlier x hxLater
  omega

/-- The certificate-free cross-gap target at the first diagonal boundary.

Two weakly separated four-caps reserve at least seven vertices of the upper
child.  At a singleton deep-below root, either a forbidden `(5,6,6)` outcome
already occurs in the parent or at most seven upper-child vertices remain
outside the two witnesses.

The proof below does not use `decomposableStateUpper_566`,
`decomposableExactUpperAt_six`, or their finite-certificate consequences. -/
def SingletonRootSeparatedCapChargeAtSix : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {upper earlier later : Finset (Fin n)}
      {q : Fin n},
    IsDecomposableOn χ upper → HasDeepBelowSplit χ {q} upper →
      earlier ⊆ upper → later ⊆ upper →
      earlier.card = 4 → later.card = 4 →
      IsCapSet χ earlier → IsCapSet χ later →
      FinsetWeaklyBefore earlier later →
        ContainsCapSet χ ({q} ∪ upper) 5 ∨
        ContainsCupSet χ ({q} ∪ upper) 6 ∨
        ContainsStrongPolygonSet χ ({q} ∪ upper) 6 ∨
        (upper \ (earlier ∪ later)).card ≤ 7

/-- The singleton-root separated-cap charge follows from the stronger five-cap
obstruction and therefore needs neither decomposability nor a finite
certificate. -/
theorem singletonRootSeparatedCapChargeAtSix : SingletonRootSeparatedCapChargeAtSix := by
  intro n χ upper earlier later q _hupper hroot hearlierSub hlaterSub
    hearlierCard hlaterCard hearlierCap hlaterCap hbefore
  exact Or.inl (hroot.containsCapSet_five_of_separated_upper_four_caps
    hearlierSub hlaterSub hearlierCard hlaterCard hearlierCap hlaterCap hbefore)

/-- In an open singleton-root parent, the proposed charge leaves at most seven
upper-child vertices outside the two separated four-cap witnesses. -/
theorem upper_exterior_card_le_seven_of_singletonRootSeparatedCapCharge
    (hcharge : SingletonRootSeparatedCapChargeAtSix)
    {n : ℕ} {χ : TripleColoring n} {upper earlier later : Finset (Fin n)}
    {q : Fin n} (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hearlierSub : earlier ⊆ upper) (hlaterSub : later ⊆ upper)
    (hearlierCard : earlier.card = 4) (hlaterCard : later.card = 4)
    (hearlierCap : IsCapSet χ earlier) (hlaterCap : IsCapSet χ later)
    (hbefore : FinsetWeaklyBefore earlier later)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 6) :
    (upper \ (earlier ∪ later)).card ≤ 7 := by
  rcases hcharge hupper hroot hearlierSub hlaterSub hearlierCard hlaterCard
      hearlierCap hlaterCap hbefore with hcap | hcup | hstrong | hbound
  · exact (hnoCap hcap).elim
  · exact (hnoCup hcup).elim
  · exact (hnoStrong hstrong).elim
  · exact hbound

/-- The singleton-root charge has exactly the desired numerical strength: it
replaces the independent-side bound `23` by the diagonal threshold `16`. -/
theorem singleton_root_card_le_sixteen_of_separatedCapCharge
    (hcharge : SingletonRootSeparatedCapChargeAtSix)
    {n : ℕ} {χ : TripleColoring n} {upper earlier later : Finset (Fin n)}
    {q : Fin n} (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hearlierSub : earlier ⊆ upper) (hlaterSub : later ⊆ upper)
    (hearlierCard : earlier.card = 4) (hlaterCard : later.card = 4)
    (hearlierCap : IsCapSet χ earlier) (hlaterCap : IsCapSet χ later)
    (hbefore : FinsetWeaklyBefore earlier later)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 6)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 6) :
    ({q} ∪ upper).card ≤ 16 := by
  have hexterior : (upper \ (earlier ∪ later)).card ≤ 7 :=
    upper_exterior_card_le_seven_of_singletonRootSeparatedCapCharge hcharge
      hupper hroot hearlierSub hlaterSub hearlierCard hlaterCard hearlierCap
      hlaterCap hbefore hnoCap hnoCup hnoStrong
  have hunionSub : earlier ∪ later ⊆ upper :=
    Finset.union_subset hearlierSub hlaterSub
  have hunionCard : (earlier ∪ later).card ≤ 8 := by
    calc
      (earlier ∪ later).card ≤ earlier.card + later.card :=
        Finset.card_union_le earlier later
      _ = 8 := by omega
  have hupperSplit := Finset.card_sdiff_add_card_eq_card hunionSub
  have hupperCard : upper.card ≤ 15 := by omega
  rw [Finset.card_union_of_disjoint hroot.disjoint]
  simp
  omega

end ErdosSzekeres

end
