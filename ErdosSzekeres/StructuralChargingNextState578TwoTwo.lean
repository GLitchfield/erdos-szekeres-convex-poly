module

public import ErdosSzekeres.StructuralChargingNextState578OpenSpan

@[expose] public section

/-!
# The two-plus-two terminal-cap branch at state `(5,7,8)`

This file couples the terminal-cap tail reservoir to the cap's unique lowest
separating decomposition-tree node.  It then audits how much of the terminal
bridge information survives in the unresolved `2+2` branch.
-/

namespace ErdosSzekeres

/-- Candidate local consumer for the five-internal-tail side of the terminal
`2+2` dichotomy.  It is stated explicitly so a bounded counterexample can
retire exactly this amount of local information without touching the full
32-vertex singleton-lower gate. -/
def FiveInternalOuterTailGate578 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {lower upper cap tails : Finset (Fin n)},
    HasDeepBelowSplit χ lower upper →
    (hcap : cap ∈ capWitnesses χ (lower ∪ upper) 4) →
    (cap ∩ lower).card = 2 →
    (cap ∩ upper).card = 2 →
    ¬ContainsCupSet χ lower 6 →
    (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ (lower ∪ upper) 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap))) →
    tails ⊆ (((lower ∪ upper) \ openSweepSpanVertices (lower ∪ upper) cap
      (capWitness_nonempty_of_mem (by omega) hcap)) \ cap) →
    tails.card = 5 →
    ContainsCapSet χ (lower ∪ upper) 5 ∨
      ContainsCupSet χ (lower ∪ upper) 7 ∨
      ContainsStrongPolygonSet χ (lower ∪ upper) 8

/-- The same terminal four-cap simultaneously carries the nine genuine
outer-tail bridges and the lowest-split `1+3`/`2+2` alternative.  In the
`1+3` branch, the strict `(5,5,8)` predecessor bounds the lower child by 20. -/
theorem exists_terminalFourCap_nineTail_lowestSplit_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hupperCard : upper.card = 32)
    (hstate558 : DecomposableStateUpper 5 5 8)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ upper 4,
      (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ upper 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))) ∧
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val ∧
      9 ≤ ((upper \ openSweepSpanVertices upper cap
        (capWitness_nonempty_of_mem (by omega) hcap)) \ cap).card ∧
      (∀ x ∈ (upper \ openSweepSpanVertices upper cap
          (capWitness_nonempty_of_mem (by omega) hcap)) \ cap,
        RealizesCapFourFailureSignature χ cap
            (mem_capWitnesses.mp hcap).2.1 x .before ∨
          RealizesCapFourFailureSignature χ cap
            (mem_capWitnesses.mp hcap).2.1 x .after) ∧
      ∃ tree : DecompositionTree χ upper,
        ∃ path : List Bool, ∃ node : DecompositionSplit χ,
        tree.splitAtPath path = some node ∧
        DecompositionTree.IsLowestSeparatingPath cap tree path ∧
        (((cap ∩ node.lower).card = 1 ∧
            (cap ∩ node.upper).card = 3 ∧
            ¬ContainsCupSet χ node.lower 5 ∧ node.lower.card ≤ 20) ∨
          ((cap ∩ node.lower).card = 2 ∧
            (cap ∩ node.upper).card = 2 ∧
            ¬ContainsCupSet χ node.lower 6)) := by
  obtain ⟨cap, hcap, hterminal, hstraddles, htail, hbridge⟩ :=
    exists_terminal_straddling_fourCap_nineTailBridge_at_578
      hupper hroot hupperCard hnoCap hnoCup hnoStrong
  obtain ⟨tree⟩ := DecompositionTree.exists_of_isDecomposableOn hupper
  have hnoCapUpper : ¬ContainsCapSet χ upper 5 := fun hcapUpper ↦
    hnoCap (FinsetPolygon.ContainsCapSet.mono hcapUpper Finset.subset_union_right)
  have hnoStrongUpper : ¬ContainsStrongPolygonSet χ upper 8 := fun hstrongUpper ↦
    hnoStrong (FinsetPolygon.ContainsStrongPolygonSet.mono hstrongUpper
      Finset.subset_union_right)
  obtain ⟨path, node, hlookup, hallocated, halternative⟩ :=
    fourCap_lowestSplit_openAlternative_of_state_558
      tree hcap hstate558 hnoCapUpper hnoStrongUpper
  exact ⟨cap, hcap, hterminal, hstraddles, htail, hbridge,
    tree, path, node, hlookup, hallocated, halternative⟩

/-- A cap crossing a deep split in a `2+2` profile has a unique child word:
its two sweep endpoints lie in the lower child and its two middle vertices lie
in the upper child. -/
theorem capFour_twoTwo_deepSplit_membership
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cap : Finset (Fin n)}
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hcap : cap ∈ capWitnesses χ (lower ∪ upper) 4)
    (hlowerCard : (cap ∩ lower).card = 2)
    (hupperCard : (cap ∩ upper).card = 2) :
    let c := cap.orderEmbOfFin (mem_capWitnesses.mp hcap).2.1
    c 0 ∈ lower ∧ c 1 ∈ upper ∧ c 2 ∈ upper ∧ c 3 ∈ lower := by
  let hcapCard := (mem_capWitnesses.mp hcap).2.1
  let c := cap.orderEmbOfFin hcapCard
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
      (hnotLower : ¬(i ∈ lower ∧ j ∈ lower ∧ k ∈ lower))
      (hnotUpper : ¬(i ∈ upper ∧ j ∈ upper ∧ k ∈ upper)) : False := by
    have hcross := hsplit.crossing ⟨i, j, k, hij, hjk⟩
      hiUnion hjUnion hkUnion hnotLower hnotUpper
    rw [if_pos hjLower] at hcross
    have hright := hcapSet ⟨i, j, k, hij, hjk⟩ hiCap hjCap hkCap
    exact Turn.noConfusion (hcross.symm.trans hright)
  have hthree012 : ({c 0, c 1, c 2} : Finset (Fin n)).card = 3 := by
    have h01 : c 0 ≠ c 1 := ne_of_lt (c.strictMono (by decide))
    have h02 : c 0 ≠ c 2 := ne_of_lt (c.strictMono (by decide))
    have h12 : c 1 ≠ c 2 := ne_of_lt (c.strictMono (by decide))
    simp [h01, h02, h12]
  have hthree123 : ({c 1, c 2, c 3} : Finset (Fin n)).card = 3 := by
    have h12 : c 1 ≠ c 2 := ne_of_lt (c.strictMono (by decide))
    have h13 : c 1 ≠ c 3 := ne_of_lt (c.strictMono (by decide))
    have h23 : c 2 ≠ c 3 := ne_of_lt (c.strictMono (by decide))
    simp [h12, h13, h23]
  have hc1Upper : c 1 ∈ upper := by
    rcases Finset.mem_union.mp (hcUnion 1) with hc1Lower | hc1Upper
    · rcases Finset.mem_union.mp (hcUnion 0) with hc0Lower | hc0Upper <;>
        rcases Finset.mem_union.mp (hcUnion 2) with hc2Lower | hc2Upper
      · have hsubset : ({c 0, c 1, c 2} : Finset (Fin n)) ⊆ cap ∩ lower := by
          simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
            Finset.mem_inter]
          exact ⟨⟨hcMem 0, hc0Lower⟩, ⟨hcMem 1, hc1Lower⟩,
            ⟨hcMem 2, hc2Lower⟩⟩
        have hcardLe := Finset.card_le_card hsubset
        omega
      · exact False.elim (crossing_middle_lower_false
          (c.strictMono (by decide)) (c.strictMono (by decide))
          (hcMem 0) (hcMem 1) (hcMem 2)
          (hcUnion 0) (hcUnion 1) (hcUnion 2) hc1Lower
          (fun h ↦ hdisjoint h.2.2 hc2Upper)
          (fun h ↦ hdisjoint hc0Lower h.1))
      · exact False.elim (crossing_middle_lower_false
          (c.strictMono (by decide)) (c.strictMono (by decide))
          (hcMem 0) (hcMem 1) (hcMem 2)
          (hcUnion 0) (hcUnion 1) (hcUnion 2) hc1Lower
          (fun h ↦ hdisjoint h.1 hc0Upper)
          (fun h ↦ hdisjoint hc2Lower h.2.2))
      · exact False.elim (crossing_middle_lower_false
          (c.strictMono (by decide)) (c.strictMono (by decide))
          (hcMem 0) (hcMem 1) (hcMem 2)
          (hcUnion 0) (hcUnion 1) (hcUnion 2) hc1Lower
          (fun h ↦ hdisjoint h.1 hc0Upper)
          (fun h ↦ hdisjoint hc1Lower h.2.1))
    · exact hc1Upper
  have hc2Upper : c 2 ∈ upper := by
    rcases Finset.mem_union.mp (hcUnion 2) with hc2Lower | hc2Upper
    · rcases Finset.mem_union.mp (hcUnion 3) with hc3Lower | hc3Upper
      · exact False.elim (crossing_middle_lower_false
          (c.strictMono (by decide)) (c.strictMono (by decide))
          (hcMem 1) (hcMem 2) (hcMem 3)
          (hcUnion 1) (hcUnion 2) (hcUnion 3) hc2Lower
          (fun h ↦ hdisjoint h.1 hc1Upper)
          (fun h ↦ hdisjoint hc2Lower h.2.1))
      · exact False.elim (crossing_middle_lower_false
          (c.strictMono (by decide)) (c.strictMono (by decide))
          (hcMem 1) (hcMem 2) (hcMem 3)
          (hcUnion 1) (hcUnion 2) (hcUnion 3) hc2Lower
          (fun h ↦ hdisjoint h.1 hc1Upper)
          (fun h ↦ hdisjoint hc2Lower h.2.1))
    · exact hc2Upper
  have hc0Lower : c 0 ∈ lower := by
    rcases Finset.mem_union.mp (hcUnion 0) with hc0Lower | hc0Upper
    · exact hc0Lower
    · have hsubset : ({c 0, c 1, c 2} : Finset (Fin n)) ⊆ cap ∩ upper := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
          Finset.mem_inter]
        exact ⟨⟨hcMem 0, hc0Upper⟩, ⟨hcMem 1, hc1Upper⟩,
          ⟨hcMem 2, hc2Upper⟩⟩
      have hcardLe := Finset.card_le_card hsubset
      omega
  have hc3Lower : c 3 ∈ lower := by
    rcases Finset.mem_union.mp (hcUnion 3) with hc3Lower | hc3Upper
    · exact hc3Lower
    · have hsubset : ({c 1, c 2, c 3} : Finset (Fin n)) ⊆ cap ∩ upper := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
          Finset.mem_inter]
        exact ⟨⟨hcMem 1, hc1Upper⟩, ⟨hcMem 2, hc2Upper⟩,
          ⟨hcMem 3, hc3Upper⟩⟩
      have hcardLe := Finset.card_le_card hsubset
      omega
  exact ⟨hc0Lower, hc1Upper, hc2Upper, hc3Lower⟩

/-- In the `2+2` cap profile, the terminal bridge of any vertex before the
cap and still inside the lowest node is forced by the deep-split law alone. -/
theorem capFour_twoTwo_deepSplit_forces_before_bridge
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cap : Finset (Fin n)} {x : Fin n}
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hcap : cap ∈ capWitnesses χ (lower ∪ upper) 4)
    (hlowerCard : (cap ∩ lower).card = 2)
    (hupperCard : (cap ∩ upper).card = 2)
    (hx : x ∈ lower ∪ upper)
    (hbefore : x < cap.orderEmbOfFin (mem_capWitnesses.mp hcap).2.1 0) :
    RealizesCapFourFailureSignature χ cap
      (mem_capWitnesses.mp hcap).2.1 x .before := by
  let hcapCard := (mem_capWitnesses.mp hcap).2.1
  let c := cap.orderEmbOfFin hcapCard
  obtain ⟨hc0Lower, hc1Upper, _hc2Upper, _hc3Lower⟩ :=
    capFour_twoTwo_deepSplit_membership hsplit hcap hlowerCard hupperCard
  have hc0Union : c 0 ∈ lower ∪ upper :=
    (mem_capWitnesses.mp hcap).1 (cap.orderEmbOfFin_mem hcapCard 0)
  have hc1Union : c 1 ∈ lower ∪ upper :=
    (mem_capWitnesses.mp hcap).1 (cap.orderEmbOfFin_mem hcapCard 1)
  have hdisjoint := Finset.disjoint_left.mp hsplit.disjoint
  refine ⟨hbefore, ?_⟩
  have hcross := hsplit.crossing
    ⟨x, c 0, c 1, hbefore, c.strictMono (by decide)⟩
    hx hc0Union hc1Union
    (fun h ↦ hdisjoint h.2.2 hc1Upper)
    (fun h ↦ hdisjoint hc0Lower h.2.1)
  rw [if_pos hc0Lower] at hcross
  simpa [c, hcapCard] using hcross

/-- In the `2+2` cap profile, the terminal bridge of any vertex after the cap
and still inside the lowest node is likewise forced by the deep-split law. -/
theorem capFour_twoTwo_deepSplit_forces_after_bridge
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cap : Finset (Fin n)} {x : Fin n}
    (hsplit : HasDeepBelowSplit χ lower upper)
    (hcap : cap ∈ capWitnesses χ (lower ∪ upper) 4)
    (hlowerCard : (cap ∩ lower).card = 2)
    (hupperCard : (cap ∩ upper).card = 2)
    (hx : x ∈ lower ∪ upper)
    (hafter : cap.orderEmbOfFin (mem_capWitnesses.mp hcap).2.1 3 < x) :
    RealizesCapFourFailureSignature χ cap
      (mem_capWitnesses.mp hcap).2.1 x .after := by
  let hcapCard := (mem_capWitnesses.mp hcap).2.1
  let c := cap.orderEmbOfFin hcapCard
  obtain ⟨_hc0Lower, _hc1Upper, hc2Upper, hc3Lower⟩ :=
    capFour_twoTwo_deepSplit_membership hsplit hcap hlowerCard hupperCard
  have hc2Union : c 2 ∈ lower ∪ upper :=
    (mem_capWitnesses.mp hcap).1 (cap.orderEmbOfFin_mem hcapCard 2)
  have hc3Union : c 3 ∈ lower ∪ upper :=
    (mem_capWitnesses.mp hcap).1 (cap.orderEmbOfFin_mem hcapCard 3)
  have hdisjoint := Finset.disjoint_left.mp hsplit.disjoint
  refine ⟨hafter, ?_⟩
  have hcross := hsplit.crossing
    ⟨c 2, c 3, x, c.strictMono (by decide), hafter⟩
    hc2Union hc3Union hx
    (fun h ↦ hdisjoint h.1 hc2Upper)
    (fun h ↦ hdisjoint hc3Lower h.2.1)
  rw [if_pos hc3Lower] at hcross
  simpa [c, hcapCard] using hcross

/-- Nine vertices partitioned by any finite region leave at least five on one
side of the partition. -/
theorem five_le_inter_or_sdiff_of_nine_le_card
    {α : Type*} [DecidableEq α] (s region : Finset α)
    (hcard : 9 ≤ s.card) :
    5 ≤ (s ∩ region).card ∨ 5 ≤ (s \ region).card := by
  have hpartition := Finset.card_sdiff_add_card_inter s region
  omega

/-- Relative to the lowest node of a terminal cap, at least five of the nine
genuine tail vertices stay inside that node or at least five escape above it. -/
theorem terminalOuterTail_five_inside_or_outside
    {n : ℕ} {χ : TripleColoring n}
    {support cap : Finset (Fin n)}
    (hcap : cap ∈ capWitnesses χ support 4)
    (node : DecompositionSplit χ)
    (htail : 9 ≤ ((support \ openSweepSpanVertices support cap
      (capWitness_nonempty_of_mem (by omega) hcap)) \ cap).card) :
    let tail := (support \ openSweepSpanVertices support cap
      (capWitness_nonempty_of_mem (by omega) hcap)) \ cap
    5 ≤ (tail ∩ (node.lower ∪ node.upper)).card ∨
      5 ≤ (tail \ (node.lower ∪ node.upper)).card := by
  exact five_le_inter_or_sdiff_of_nine_le_card _ _ htail

namespace DecompositionTree

/-- The first place where `x` leaves the branch containing the whole cap while
following a fixed tree path.  The final Boolean records whether the cap branch
at that exit is the lower (`false`) or upper (`true`) child. -/
inductive FirstExitAlongPath {n : ℕ} {χ : TripleColoring n}
    (cap : Finset (Fin n)) (x : Fin n) :
    {support : Finset (Fin n)} → DecompositionTree χ support →
      List Bool → Bool → Prop
  | lowerHere {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper) {suffix : List Bool}
      (hcap : cap ⊆ lower) (hx : x ∈ upper) :
      FirstExitAlongPath cap x (.split lowerTree upperTree deep)
        (false :: suffix) false
  | upperHere {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper) {suffix : List Bool}
      (hcap : cap ⊆ upper) (hx : x ∈ lower) :
      FirstExitAlongPath cap x (.split lowerTree upperTree deep)
        (true :: suffix) true
  | lowerBelow {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper) {suffix : List Bool}
      {exitDirection : Bool} (hcap : cap ⊆ lower) (hx : x ∈ lower)
      (below : FirstExitAlongPath cap x lowerTree suffix exitDirection) :
      FirstExitAlongPath cap x (.split lowerTree upperTree deep)
        (false :: suffix) exitDirection
  | upperBelow {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper) {suffix : List Bool}
      {exitDirection : Bool} (hcap : cap ⊆ upper) (hx : x ∈ upper)
      (below : FirstExitAlongPath cap x upperTree suffix exitDirection) :
      FirstExitAlongPath cap x (.split lowerTree upperTree deep)
        (true :: suffix) exitDirection

/-- At a deep split, an endpoint bridge cannot put the whole cap in the upper
child while its bridge vertex lies in the lower child. -/
theorem upperExit_impossible_of_endpoint_bridge
    {n : ℕ} {χ : TripleColoring n}
    {lower upper cap : Finset (Fin n)} {x : Fin n}
    (deep : HasDeepBelowSplit χ lower upper)
    (hcapCard : cap.card = 4) (hcapUpper : cap ⊆ upper)
    (hxLower : x ∈ lower)
    (hbridge : RealizesCapFourFailureSignature χ cap hcapCard x .before ∨
      RealizesCapFourFailureSignature χ cap hcapCard x .after) : False := by
  let c := cap.orderEmbOfFin hcapCard
  have hcUpper (i : Fin 4) : c i ∈ upper :=
    hcapUpper (cap.orderEmbOfFin_mem hcapCard i)
  have hxUnion : x ∈ lower ∪ upper := Finset.mem_union_left _ hxLower
  have hcUnion (i : Fin 4) : c i ∈ lower ∪ upper :=
    Finset.mem_union_right _ (hcUpper i)
  have hdisjoint := Finset.disjoint_left.mp deep.disjoint
  rcases hbridge with hbefore | hafter
  · obtain ⟨hx0, hleft⟩ := hbefore
    have hcross := deep.crossing
      ⟨x, c 0, c 1, hx0, c.strictMono (by decide)⟩
      hxUnion (hcUnion 0) (hcUnion 1)
      (fun h ↦ hdisjoint h.2.1 (hcUpper 0))
      (fun h ↦ hdisjoint hxLower h.1)
    rw [if_neg (fun hc0Lower ↦ hdisjoint hc0Lower (hcUpper 0))] at hcross
    exact Turn.noConfusion (hcross.symm.trans hleft)
  · obtain ⟨h3x, hleft⟩ := hafter
    have hcross := deep.crossing
      ⟨c 2, c 3, x, c.strictMono (by decide), h3x⟩
      (hcUnion 2) (hcUnion 3) hxUnion
      (fun h ↦ hdisjoint h.1 (hcUpper 2))
      (fun h ↦ hdisjoint hxLower h.2.2)
    rw [if_neg (fun hc3Lower ↦ hdisjoint hc3Lower (hcUpper 3))] at hcross
    exact Turn.noConfusion (hcross.symm.trans hleft)

/-- Endpoint-bridge information orients every first exit: the cap branch at
the first separating split is necessarily the lower child. -/
theorem FirstExitAlongPath.direction_eq_false_of_endpoint_bridge
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {x : Fin n} {exitDirection : Bool}
    (hexit : FirstExitAlongPath cap x tree path exitDirection)
    (hcapCard : cap.card = 4)
    (hbridge : RealizesCapFourFailureSignature χ cap hcapCard x .before ∨
      RealizesCapFourFailureSignature χ cap hcapCard x .after) :
    exitDirection = false := by
  induction hexit with
  | lowerHere => rfl
  | upperHere lowerTree upperTree deep hcapUpper hxLower =>
      exact False.elim
        (upperExit_impossible_of_endpoint_bridge deep hcapCard hcapUpper
          hxLower hbridge)
  | lowerBelow _lowerTree _upperTree _deep _hcap _hx _below ih => exact ih
  | upperBelow _lowerTree _upperTree _deep _hcap _hx _below ih => exact ih

/-- A vertex in the root support but outside the node reached by a cap path
has a well-defined first exit from that path. -/
theorem exists_firstExitAlongPath
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ} {x : Fin n}
    (hlookup : tree.splitAtPath path = some node)
    (hcapNode : cap ⊆ node.lower ∪ node.upper)
    (hxSupport : x ∈ support)
    (hxOutside : x ∉ node.lower ∪ node.upper) :
    ∃ exitDirection,
      FirstExitAlongPath cap x tree path exitDirection := by
  induction tree generalizing path node with
  | singleton i =>
      cases path <;> simp [splitAtPath] at hlookup
  | @split lower upper lowerTree upperTree deep ihLower ihUpper =>
      cases path with
      | nil =>
          simp only [splitAtPath, Option.some.injEq] at hlookup
          subst node
          exact False.elim (hxOutside hxSupport)
      | cons direction suffix =>
          cases direction
          · have hchildLookup : lowerTree.splitAtPath suffix = some node := by
              simpa [splitAtPath] using hlookup
            have hnodeSub : node.lower ∪ node.upper ⊆ lower :=
              lowerTree.splitAtPath_support_subset hchildLookup
            have hcapLower : cap ⊆ lower := hcapNode.trans hnodeSub
            rcases Finset.mem_union.mp hxSupport with hxLower | hxUpper
            · obtain ⟨exitDirection, hexit⟩ :=
                ihLower hchildLookup hcapNode hxLower hxOutside
              exact ⟨exitDirection,
                .lowerBelow lowerTree upperTree deep hcapLower hxLower hexit⟩
            · exact ⟨false,
                .lowerHere lowerTree upperTree deep hcapLower hxUpper⟩
          · have hchildLookup : upperTree.splitAtPath suffix = some node := by
              simpa [splitAtPath] using hlookup
            have hnodeSub : node.lower ∪ node.upper ⊆ upper :=
              upperTree.splitAtPath_support_subset hchildLookup
            have hcapUpper : cap ⊆ upper := hcapNode.trans hnodeSub
            rcases Finset.mem_union.mp hxSupport with hxLower | hxUpper
            · exact ⟨true,
                .upperHere lowerTree upperTree deep hcapUpper hxLower⟩
            · obtain ⟨exitDirection, hexit⟩ :=
                ihUpper hchildLookup hcapNode hxUpper hxOutside
              exact ⟨exitDirection,
                .upperBelow lowerTree upperTree deep hcapUpper hxUpper hexit⟩

/-- A vertex outside the lowest cap node with an endpoint bridge has a first
exit whose cap branch is definitionally normalized to the lower child. -/
theorem exists_false_firstExitAlongPath_of_endpoint_bridge
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ} {x : Fin n}
    (hlookup : tree.splitAtPath path = some node)
    (hallocated : IsLowestSeparatingPath cap tree path)
    (hcapCard : cap.card = 4)
    (hxSupport : x ∈ support)
    (hxOutside : x ∉ node.lower ∪ node.upper)
    (hbridge : RealizesCapFourFailureSignature χ cap hcapCard x .before ∨
      RealizesCapFourFailureSignature χ cap hcapCard x .after) :
    FirstExitAlongPath cap x tree path false := by
  have hcapNode := (hallocated.splitAtPath_spec hlookup).1
  obtain ⟨direction, hexit⟩ :=
    exists_firstExitAlongPath tree hlookup hcapNode hxSupport hxOutside
  have hdirection :=
    hexit.direction_eq_false_of_endpoint_bridge hcapCard hbridge
  simpa [hdirection] using hexit

/-- A prefix addresses a lower-cap exit when it resolves to a split with the
whole cap below and the escaping vertex above. -/
def IsLowerExitAddress {n : ℕ} {χ : TripleColoring n}
    {support : Finset (Fin n)} (cap : Finset (Fin n)) (x : Fin n)
    (tree : DecompositionTree χ support) (address : List Bool) : Prop :=
  ∃ node : DecompositionSplit χ,
    tree.splitAtPath address = some node ∧ cap ⊆ node.lower ∧ x ∈ node.upper

/-- Every lower-directed first exit exposes a concrete prefix and split node
at which the cap lies below and the escaping vertex lies above. -/
theorem FirstExitAlongPath.exists_lowerExitAddress
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool} {x : Fin n}
    {exitDirection : Bool}
    (hexit : FirstExitAlongPath cap x tree path exitDirection)
    (hdirection : exitDirection = false) :
    ∃ address suffix,
      path = address ++ false :: suffix ∧ IsLowerExitAddress cap x tree address := by
  induction hexit with
  | lowerHere lowerTree upperTree deep hcap hx =>
      refine ⟨[], _, rfl, ?_⟩
      exact ⟨⟨_, _, deep⟩, by simp [splitAtPath], hcap, hx⟩
  | upperHere => exact Bool.noConfusion hdirection
  | lowerBelow lowerTree upperTree deep hcap hx below ih =>
      obtain ⟨address, tail, hpath, node, hlookup, hcapNode, hxNode⟩ :=
        ih hdirection
      refine ⟨false :: address, tail, ?_, ?_⟩
      · simp only [List.cons_append]
        rw [hpath]
      · exact ⟨node, by simpa [splitAtPath] using hlookup, hcapNode, hxNode⟩
  | upperBelow lowerTree upperTree deep hcap hx below ih =>
      obtain ⟨address, tail, hpath, node, hlookup, hcapNode, hxNode⟩ :=
        ih hdirection
      refine ⟨true :: address, tail, ?_, ?_⟩
      · simp only [List.cons_append]
        rw [hpath]
      · exact ⟨node, by simpa [splitAtPath] using hlookup, hcapNode, hxNode⟩

end DecompositionTree

/-- Five endpoint-bridge tails either remain in the selected cap node or five
tails leave it, each with a certified lower-branch first exit. -/
theorem five_inside_or_five_falseFirstExit
    {n : ℕ} {χ : TripleColoring n} {support cap tails : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node)
    (hallocated : DecompositionTree.IsLowestSeparatingPath cap tree path)
    (hcapCard : cap.card = 4)
    (htailsCard : 9 ≤ tails.card) (htailsSupport : tails ⊆ support)
    (hbridge : ∀ x ∈ tails,
      RealizesCapFourFailureSignature χ cap hcapCard x .before ∨
        RealizesCapFourFailureSignature χ cap hcapCard x .after) :
    5 ≤ (tails ∩ (node.lower ∪ node.upper)).card ∨
      (5 ≤ (tails \ (node.lower ∪ node.upper)).card ∧
        ∀ x ∈ tails \ (node.lower ∪ node.upper),
          DecompositionTree.FirstExitAlongPath cap x tree path false ∧
            ∃ address suffix,
              path = address ++ false :: suffix ∧
                DecompositionTree.IsLowerExitAddress cap x tree address) := by
  rcases five_le_inter_or_sdiff_of_nine_le_card tails
      (node.lower ∪ node.upper) htailsCard with hinside | houtside
  · exact Or.inl hinside
  · refine Or.inr ⟨houtside, ?_⟩
    intro x hx
    have hxData := Finset.mem_sdiff.mp hx
    have hfirst := DecompositionTree.exists_false_firstExitAlongPath_of_endpoint_bridge
      tree hlookup hallocated hcapCard (htailsSupport hxData.1) hxData.2
      (hbridge x hxData.1)
    exact ⟨hfirst, hfirst.exists_lowerExitAddress rfl⟩

/-- The exact unresolved tail alternative attached to a lowest cap node. -/
def TwoTwoTailLocalization578 {n : ℕ} (χ : TripleColoring n)
    (support cap : Finset (Fin n)) (hcapCard : cap.card = 4)
    (tree : DecompositionTree χ support) (path : List Bool)
    (node : DecompositionSplit χ) : Prop :=
  let tails := (support \ openSweepSpanVertices support cap
    (Finset.card_pos.mp (by omega : 0 < cap.card))) \ cap
  5 ≤ (tails ∩ (node.lower ∪ node.upper)).card ∨
    (5 ≤ (tails \ (node.lower ∪ node.upper)).card ∧
      ∀ x ∈ tails \ (node.lower ∪ node.upper),
        DecompositionTree.FirstExitAlongPath cap x tree path false ∧
          ∃ address suffix,
            path = address ++ false :: suffix ∧
              DecompositionTree.IsLowerExitAddress cap x tree address)

/-- In the actual singleton-lower `(5,7,8)` obstruction, one terminal cap has
either the bounded `1+3` node or a `2+2` node carrying the exact five-tail
inside/false-first-exit residual. -/
theorem exists_terminalFourCap_lowestSplit_tailResidual_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hupperCard : upper.card = 32)
    (hstate558 : DecomposableStateUpper 5 5 8)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ upper 4,
      (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ upper 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))) ∧
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val ∧
      ∃ tree : DecompositionTree χ upper,
        ∃ path : List Bool, ∃ node : DecompositionSplit χ,
        tree.splitAtPath path = some node ∧
        DecompositionTree.IsLowestSeparatingPath cap tree path ∧
        (((cap ∩ node.lower).card = 1 ∧
            (cap ∩ node.upper).card = 3 ∧
            ¬ContainsCupSet χ node.lower 5 ∧ node.lower.card ≤ 20) ∨
          (((cap ∩ node.lower).card = 2 ∧
              (cap ∩ node.upper).card = 2 ∧
              ¬ContainsCupSet χ node.lower 6) ∧
            TwoTwoTailLocalization578 χ upper cap
              (mem_capWitnesses.mp hcap).2.1 tree path node)) := by
  obtain ⟨cap, hcap, hterminal, hstraddles, htail, hbridge,
      tree, path, node, hlookup, hallocated, halternative⟩ :=
    exists_terminalFourCap_nineTail_lowestSplit_at_578
      hupper hroot hupperCard hstate558 hnoCap hnoCup hnoStrong
  let tails := (upper \ openSweepSpanVertices upper cap
    (capWitness_nonempty_of_mem (by omega) hcap)) \ cap
  have htailSupport : tails ⊆ upper := by
    intro x hx
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
  have hlocalization := five_inside_or_five_falseFirstExit tree hlookup
    hallocated (mem_capWitnesses.mp hcap).2.1 htail htailSupport hbridge
  refine ⟨cap, hcap, hterminal, hstraddles, tree, path, node, hlookup,
    hallocated, ?_⟩
  rcases halternative with hOneThree | hTwoTwo
  · exact Or.inl hOneThree
  · exact Or.inr ⟨hTwoTwo, by
      simpa [TwoTwoTailLocalization578, tails] using hlocalization⟩

end ErdosSzekeres

end
