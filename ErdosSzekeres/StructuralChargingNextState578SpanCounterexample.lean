module

public import ErdosSzekeres.StructuralChargingNextState578Threshold

@[expose] public section

/-!
# Exact dense common-cut counterexample at 32 vertices

The strict-span descent contract is false at its exact `32/23` constants.
This file constructs a recursively decomposable coloring on three consecutive
blocks of sizes `11, 11, 10`.  At the root the first and third blocks form the
lower child, while the middle block is the upper child; both children are
cup-colored.  Its four-caps have the exact block pattern `A-B-B-A`.
-/

namespace ErdosSzekeres

/-- Every nonempty cup-colored finite set is recursively decomposable.  Peel
its minimum vertex as the upper singleton at each step. -/
theorem FinsetPolygon.IsCupSet.isDecomposableOn_of_nonempty
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hcup : IsCupSet χ s) (hs : s.Nonempty) :
    IsDecomposableOn χ s := by
  classical
  refine Finset.strongInductionOn s
    (p := fun carrier ↦
      IsCupSet χ carrier → carrier.Nonempty →
        IsDecomposableOn χ carrier) ?_ hcup hs
  intro carrier ih hcarrierCup hcarrier
  by_cases hcard : carrier.card = 1
  · obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hcard
    exact .singleton q
  · let q := carrier.min' hcarrier
    have hq : q ∈ carrier := Finset.min'_mem carrier hcarrier
    let rest := carrier.erase q
    have hrestCard : rest.card = carrier.card - 1 :=
      Finset.card_erase_of_mem hq
    have hcarrierCard : 2 ≤ carrier.card := by
      have hpos := hcarrier.card_pos
      omega
    have hrestNonempty : rest.Nonempty := by
      rw [← Finset.card_pos, hrestCard]
      omega
    have hrestCup : IsCupSet χ rest :=
      FinsetPolygon.IsCupSet.mono hcarrierCup (by
        simpa [rest] using Finset.erase_subset q carrier)
    have hrestDecomposable : IsDecomposableOn χ rest :=
      ih rest (Finset.erase_ssubset hq) hrestCup hrestNonempty
    have hunion : rest ∪ {q} = carrier := by
      simp [rest, hq]
    have hdeep : HasDeepBelowSplit χ rest {q} := by
      constructor
      · simp [rest]
      · intro t hi hj hk _hnotRest _hnotSingleton
        have hiCarrier : t.i ∈ carrier := by
          rw [← hunion]
          exact hi
        have hjCarrier : t.j ∈ carrier := by
          rw [← hunion]
          exact hj
        have hkCarrier : t.k ∈ carrier := by
          rw [← hunion]
          exact hk
        have hjRest : t.j ∈ rest := by
          rcases Finset.mem_union.mp hj with hjRest | hjq
          · exact hjRest
          · have hjEq : t.j = q := Finset.mem_singleton.mp hjq
            have hmin : q ≤ t.i :=
              Finset.min'_le carrier t.i hiCarrier
            have hiq : t.i < q := by simpa [hjEq] using t.hij
            exact (not_lt_of_ge hmin hiq).elim
        rw [if_pos hjRest]
        exact hcarrierCup t hiCarrier hjCarrier hkCarrier
    rw [← hunion]
    exact .split hrestDecomposable (.singleton q) hdeep

/-- Four vertices with lower-child sweep endpoints surrounding two
upper-child vertices always form a cap across a deep-below split. -/
theorem HasDeepBelowSplit.containsCapSet_four_of_outer_lower_inner_upper
    {n : ℕ} {χ : TripleColoring n}
    {lower upper ambient : Finset (Fin n)} {a b c d : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (haLower : a ∈ lower) (hbUpper : b ∈ upper)
    (hcUpper : c ∈ upper) (hdLower : d ∈ lower)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (haAmbient : a ∈ ambient) (hbAmbient : b ∈ ambient)
    (hcAmbient : c ∈ ambient) (hdAmbient : d ∈ ambient) :
    ContainsCapSet χ ambient 4 := by
  let g : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![a, b, c, d] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact hab
        | exact hab.trans hbc
        | exact hab.trans (hbc.trans hcd)
        | exact hbc
        | exact hbc.trans hcd
        | exact hcd)
  have hgSub : Finset.univ.image g ⊆ ambient := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i <;> simp [g, haAmbient, hbAmbient, hcAmbient, hdAmbient]
  refine ⟨Finset.univ.image g, hgSub,
    by simpa using Finset.card_image_of_injective Finset.univ g.injective,
    FinsetPolygon.IsCap.image ?_⟩
  refine ⟨g.strictMono, ?_⟩
  intro i j k hij hjk
  have hdisjoint := Finset.disjoint_left.mp hdeep.disjoint
  have right_of_middle_upper (t : OrderedTriple n)
      (hti : t.i ∈ lower ∪ upper) (htj : t.j ∈ lower ∪ upper)
      (htk : t.k ∈ lower ∪ upper) (htjUpper : t.j ∈ upper)
      (hsomeLower : t.i ∈ lower ∨ t.j ∈ lower ∨ t.k ∈ lower) :
      χ t = Turn.right := by
    have htjNotLower : t.j ∉ lower := fun htjLower ↦
      hdisjoint htjLower htjUpper
    have hnotLower :
        ¬(t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) := by
      rintro ⟨_, htjLower, _⟩
      exact htjNotLower htjLower
    have hnotUpper :
        ¬(t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper) := by
      rintro hallUpper
      rcases hsomeLower with hiLower | hjLower | hkLower
      · exact hdisjoint hiLower hallUpper.1
      · exact hdisjoint hjLower hallUpper.2.1
      · exact hdisjoint hkLower hallUpper.2.2
    simpa [htjNotLower] using
      hdeep.crossing t hti htj htk hnotLower hnotUpper
  fin_cases j
  · change i.val < 0 at hij
    omega
  · change i.val < 1 at hij
    change 1 < k.val at hjk
    have hi : i = 0 := by omega
    subst i
    have hk : k = 2 ∨ k = 3 := by omega
    rcases hk with rfl | rfl
    · simpa [g] using right_of_middle_upper
        ⟨a, b, c, hab, hbc⟩
        (Finset.mem_union_left _ haLower)
        (Finset.mem_union_right _ hbUpper)
        (Finset.mem_union_right _ hcUpper) hbUpper (Or.inl haLower)
    · simpa [g] using right_of_middle_upper
        ⟨a, b, d, hab, hbc.trans hcd⟩
        (Finset.mem_union_left _ haLower)
        (Finset.mem_union_right _ hbUpper)
        (Finset.mem_union_left _ hdLower) hbUpper (Or.inl haLower)
  · change i.val < 2 at hij
    change 2 < k.val at hjk
    have hk : k = 3 := by omega
    subst k
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simpa [g] using right_of_middle_upper
        ⟨a, c, d, hab.trans hbc, hcd⟩
        (Finset.mem_union_left _ haLower)
        (Finset.mem_union_right _ hcUpper)
        (Finset.mem_union_left _ hdLower) hcUpper (Or.inl haLower)
    · simpa [g] using right_of_middle_upper
        ⟨b, c, d, hbc, hcd⟩
        (Finset.mem_union_right _ hbUpper)
        (Finset.mem_union_right _ hcUpper)
        (Finset.mem_union_left _ hdLower) hcUpper
        (Or.inr (Or.inr hdLower))
  · change 3 < k.val at hjk
    omega

/-- Cardinality partitions across three pairwise-disjoint blocks. -/
theorem card_eq_three_inter_of_subset_union
    {n : ℕ} {s first second third : Finset (Fin n)}
    (hfirstSecond : Disjoint first second)
    (hfirstThird : Disjoint first third)
    (hsecondThird : Disjoint second third)
    (hsub : s ⊆ first ∪ second ∪ third) :
    s.card = (s ∩ first).card + (s ∩ second).card +
      (s ∩ third).card := by
  have hpartition :
      (s ∩ first) ∪ (s ∩ second) ∪ (s ∩ third) = s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases Finset.mem_union.mp (hsub hx) with hxFirstSecond | hxThird
      · rcases Finset.mem_union.mp hxFirstSecond with hxFirst | hxSecond
        · exact Or.inl (Or.inl ⟨hx, hxFirst⟩)
        · exact Or.inl (Or.inr ⟨hx, hxSecond⟩)
      · exact Or.inr ⟨hx, hxThird⟩
  have hdisjointFirstSecond :
      Disjoint (s ∩ first) (s ∩ second) :=
    hfirstSecond.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdisjointUnionThird :
      Disjoint ((s ∩ first) ∪ (s ∩ second)) (s ∩ third) := by
    rw [Finset.disjoint_left]
    intro x hxUnion hxThird
    rcases Finset.mem_union.mp hxUnion with hxFirst | hxSecond
    · exact (Finset.disjoint_left.mp hfirstThird)
        (Finset.mem_inter.mp hxFirst).2 (Finset.mem_inter.mp hxThird).2
    · exact (Finset.disjoint_left.mp hsecondThird)
        (Finset.mem_inter.mp hxSecond).2 (Finset.mem_inter.mp hxThird).2
  calc
    s.card = ((s ∩ first) ∪ (s ∩ second) ∪ (s ∩ third)).card :=
      congrArg Finset.card hpartition.symm
    _ = ((s ∩ first) ∪ (s ∩ second)).card + (s ∩ third).card :=
      Finset.card_union_of_disjoint hdisjointUnionThird
    _ = (s ∩ first).card + (s ∩ second).card +
        (s ∩ third).card := by
      rw [Finset.card_union_of_disjoint hdisjointFirstSecond]

/-- A cup and a cap can share at most two vertices: any three common vertices
would force their unique increasing triple to have both colors. -/
theorem inter_card_le_two_of_cup_cap
    {n : ℕ} {χ : TripleColoring n} {cup cap : Finset (Fin n)}
    (hcup : IsCupSet χ cup) (hcap : IsCapSet χ cap) :
    (cap ∩ cup).card ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤ (cap ∩ cup).card := by omega
  obtain ⟨three, hthreeSub, hthreeCard⟩ :=
    Finset.exists_subset_card_eq hthree
  let e : Fin 3 ↪o Fin n := three.orderEmbOfFin hthreeCard
  have heMem (i : Fin 3) : e i ∈ cap ∩ cup :=
    hthreeSub (three.orderEmbOfFin_mem hthreeCard i)
  have h01 : e 0 < e 1 := e.strictMono (by decide)
  have h12 : e 1 < e 2 := e.strictMono (by decide)
  let t : OrderedTriple n := ⟨e 0, e 1, e 2, h01, h12⟩
  have hleft : χ t = Turn.left :=
    hcup t (Finset.mem_inter.mp (heMem 0)).2
      (Finset.mem_inter.mp (heMem 1)).2
      (Finset.mem_inter.mp (heMem 2)).2
  have hright : χ t = Turn.right :=
    hcap t (Finset.mem_inter.mp (heMem 0)).1
      (Finset.mem_inter.mp (heMem 1)).1
      (Finset.mem_inter.mp (heMem 2)).1
  rw [hleft] at hright
  exact Turn.noConfusion hright

namespace DenseSpanCounterexample

def q : Fin 33 := 11

def leftBlock : Finset (Fin 33) :=
  Finset.univ.filter fun x ↦ x.val < 11

def middleBlock : Finset (Fin 33) :=
  Finset.univ.filter fun x ↦ 11 < x.val ∧ x.val < 23

def rightBlock : Finset (Fin 33) :=
  Finset.univ.filter fun x ↦ 23 ≤ x.val

def lower : Finset (Fin 33) := leftBlock ∪ rightBlock

def support : Finset (Fin 33) := lower ∪ middleBlock

def color : TripleColoring 33 := fun t ↦
  if t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower then Turn.left
  else if t.i ∈ middleBlock ∧ t.j ∈ middleBlock ∧
      t.k ∈ middleBlock then Turn.left
  else if t.j ∈ lower then Turn.left else Turn.right

theorem block_cards :
    leftBlock.card = 11 ∧ middleBlock.card = 11 ∧
      rightBlock.card = 10 := by
  decide

theorem block_disjoint :
    Disjoint leftBlock middleBlock ∧
      Disjoint leftBlock rightBlock ∧
      Disjoint middleBlock rightBlock := by
  decide

theorem lower_middle_disjoint : Disjoint lower middleBlock := by
  rw [Finset.disjoint_left]
  intro x hxLower hxMiddle
  rcases Finset.mem_union.mp hxLower with hxLeft | hxRight
  · exact Finset.disjoint_left.mp block_disjoint.1 hxLeft hxMiddle
  · exact Finset.disjoint_left.mp block_disjoint.2.2 hxMiddle hxRight

theorem support_card : support.card = 32 := by
  decide

theorem lower_cup : IsCupSet color lower := by
  intro t hi hj hk
  simp [color, hi, hj, hk]

theorem middle_cup : IsCupSet color middleBlock := by
  intro t hi hj hk
  have hiNotLower : t.i ∉ lower := fun hiLower ↦
    Finset.disjoint_left.mp lower_middle_disjoint hiLower hi
  simp [color, hi, hj, hk, hiNotLower]

theorem root_deep : HasDeepBelowSplit color lower middleBlock := by
  constructor
  · exact lower_middle_disjoint
  · intro t hi hj hk hnotLower hnotMiddle
    simp [color, hnotLower, hnotMiddle]

theorem decomposable_support : IsDecomposableOn color support := by
  exact .split
    (FinsetPolygon.IsCupSet.isDecomposableOn_of_nonempty
      lower_cup (by decide))
    (FinsetPolygon.IsCupSet.isDecomposableOn_of_nonempty
      middle_cup (by decide))
    root_deep

/-- The counterexample is not an open `(5,7,8)` state: its lower child
already contains a seven-cup.  This identifies the exact target-avoidance
hypothesis omitted by the refuted strict-span recurrence. -/
theorem containsCupSet_seven : ContainsCupSet color support 7 := by
  have hseven : 7 ≤ lower.card := by decide
  obtain ⟨cup, hcupSub, hcupCard⟩ :=
    Finset.exists_subset_card_eq hseven
  exact ⟨cup, hcupSub.trans Finset.subset_union_left, hcupCard,
    FinsetPolygon.IsCupSet.mono lower_cup hcupSub⟩

/-- Every 23-element subset of the 32-vertex support contains a four-cap.
The pigeonhole argument forces one point from each outer block and two from
the middle block, which form the block pattern `A-B-B-A`. -/
theorem dense_fourCaps :
    ∀ subset : Finset (Fin 33), subset ⊆ support →
      subset.card = 23 → ContainsCapSet color subset 4 := by
  intro subset hsubset hsubsetCard
  have hsubsetBlocks :
      subset ⊆ leftBlock ∪ middleBlock ∪ rightBlock := by
    simpa [support, lower, Finset.union_assoc, Finset.union_left_comm,
      Finset.union_comm] using hsubset
  have hcount :=
    card_eq_three_inter_of_subset_union
      block_disjoint.1 block_disjoint.2.1 block_disjoint.2.2
      hsubsetBlocks
  have hleftLe : (subset ∩ leftBlock).card ≤ 11 := by
    have hle := Finset.card_le_card
      (show subset ∩ leftBlock ⊆ leftBlock from Finset.inter_subset_right)
    rw [block_cards.1] at hle
    exact hle
  have hmiddleLe : (subset ∩ middleBlock).card ≤ 11 := by
    have hle := Finset.card_le_card
      (show subset ∩ middleBlock ⊆ middleBlock from Finset.inter_subset_right)
    rw [block_cards.2.1] at hle
    exact hle
  have hrightLe : (subset ∩ rightBlock).card ≤ 10 := by
    have hle := Finset.card_le_card
      (show subset ∩ rightBlock ⊆ rightBlock from Finset.inter_subset_right)
    rw [block_cards.2.2] at hle
    exact hle
  have hleftNonempty : (subset ∩ leftBlock).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hrightNonempty : (subset ∩ rightBlock).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hmiddleTwo : 2 ≤ (subset ∩ middleBlock).card := by
    omega
  obtain ⟨a, ha⟩ := hleftNonempty
  obtain ⟨d, hd⟩ := hrightNonempty
  obtain ⟨middleTwo, hmiddleTwoSub, hmiddleTwoCard⟩ :=
    Finset.exists_subset_card_eq hmiddleTwo
  let e : Fin 2 ↪o Fin 33 := middleTwo.orderEmbOfFin hmiddleTwoCard
  let b := e 0
  let c := e 1
  have hb : b ∈ subset ∩ middleBlock :=
    hmiddleTwoSub (middleTwo.orderEmbOfFin_mem hmiddleTwoCard 0)
  have hc : c ∈ subset ∩ middleBlock :=
    hmiddleTwoSub (middleTwo.orderEmbOfFin_mem hmiddleTwoCard 1)
  have hab : a < b := by
    have haVal := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2
    have hbVal := (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2.1
    omega
  have hbc : b < c := e.strictMono (by decide)
  have hcd : c < d := by
    have hcVal := (Finset.mem_filter.mp (Finset.mem_inter.mp hc).2).2.2
    have hdVal := (Finset.mem_filter.mp (Finset.mem_inter.mp hd).2).2
    omega
  exact root_deep.containsCapSet_four_of_outer_lower_inner_upper
    (Finset.mem_union_left _ (Finset.mem_inter.mp ha).2)
    (Finset.mem_inter.mp hb).2
    (Finset.mem_inter.mp hc).2
    (Finset.mem_union_right _ (Finset.mem_inter.mp hd).2)
    hab hbc hcd
    (Finset.mem_inter.mp ha).1
    (Finset.mem_inter.mp hb).1
    (Finset.mem_inter.mp hc).1
    (Finset.mem_inter.mp hd).1

/-- Every four-cap in the construction uses exactly two vertices from each
child of the root decomposition. -/
theorem fourCap_inter_root_cards
    (cap : Finset (Fin 33))
    (hcap : cap ∈ capWitnesses color support 4) :
    (cap ∩ lower).card = 2 ∧ (cap ∩ middleBlock).card = 2 := by
  rcases mem_capWitnesses.mp hcap with ⟨hcapSub, hcapCard, hcapSet⟩
  have hcount :
      cap.card = (cap ∩ lower).card + (cap ∩ middleBlock).card := by
    simpa [support] using
      (card_eq_three_inter_of_subset_union
        (s := cap) (first := lower) (second := middleBlock)
        (third := ∅) lower_middle_disjoint (by simp) (by simp)
        (by simpa [support] using hcapSub))
  have hlowerLe : (cap ∩ lower).card ≤ 2 :=
    inter_card_le_two_of_cup_cap lower_cup hcapSet
  have hmiddleLe : (cap ∩ middleBlock).card ≤ 2 :=
    inter_card_le_two_of_cup_cap middle_cup hcapSet
  omega

/-- Every four-cap meets both separated components of the lower child.  If
both lower vertices lay on the same side of the middle block, the endpoint
law for a deep-below split would force them to be the same vertex. -/
theorem fourCap_meets_outer_blocks
    (cap : Finset (Fin 33))
    (hcap : cap ∈ capWitnesses color support 4) :
    (cap ∩ leftBlock).Nonempty ∧ (cap ∩ rightBlock).Nonempty := by
  rcases mem_capWitnesses.mp hcap with ⟨hcapSub, _hcapCard, hcapSet⟩
  have hcapSubRoot : cap ⊆ lower ∪ middleBlock := by
    simpa [support] using hcapSub
  have hrootCards := fourCap_inter_root_cards cap hcap
  have hcapMiddle : (cap ∩ middleBlock).Nonempty := by
    rw [← Finset.card_pos, hrootCards.2]
    decide
  obtain ⟨y, hy⟩ := hcapMiddle
  have hyCap : y ∈ cap := (Finset.mem_inter.mp hy).1
  have hyMiddle : y ∈ middleBlock := (Finset.mem_inter.mp hy).2
  constructor
  · by_contra hnoLeft
    have hlowerLeOne : (cap ∩ lower).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx z hz
      have hxRightBlock : x ∈ rightBlock := by
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).2 with
          hxLeft | hxRight
        · exact (hnoLeft ⟨x, Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hx).1, hxLeft⟩⟩).elim
        · exact hxRight
      have hzRightBlock : z ∈ rightBlock := by
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hz).2 with
          hzLeft | hzRight
        · exact (hnoLeft ⟨z, Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hz).1, hzLeft⟩⟩).elim
        · exact hzRight
      have hxEndpoint := root_deep.lower_mem_cap_isSweepEndpoint
        hcapSubRoot hcapSet ⟨y, hy⟩
        (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
      have hzEndpoint := root_deep.lower_mem_cap_isSweepEndpoint
        hcapSubRoot hcapSet ⟨y, hy⟩
        (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz).2
      have hxRightEndpoint :
          HasDeepBelowSplit.IsRightSweepEndpoint cap x := by
        rcases hxEndpoint with hxLeftEndpoint | hxRightEndpoint
        · have hxy := hxLeftEndpoint y hyCap
          have hxVal := (Finset.mem_filter.mp hxRightBlock).2
          have hyVal := (Finset.mem_filter.mp hyMiddle).2.2
          omega
        · exact hxRightEndpoint
      have hzRightEndpoint :
          HasDeepBelowSplit.IsRightSweepEndpoint cap z := by
        rcases hzEndpoint with hzLeftEndpoint | hzRightEndpoint
        · have hzy := hzLeftEndpoint y hyCap
          have hzVal := (Finset.mem_filter.mp hzRightBlock).2
          have hyVal := (Finset.mem_filter.mp hyMiddle).2.2
          omega
        · exact hzRightEndpoint
      exact le_antisymm
        (hzRightEndpoint x (Finset.mem_inter.mp hx).1)
        (hxRightEndpoint z (Finset.mem_inter.mp hz).1)
    omega
  · by_contra hnoRight
    have hlowerLeOne : (cap ∩ lower).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx z hz
      have hxLeftBlock : x ∈ leftBlock := by
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).2 with
          hxLeft | hxRight
        · exact hxLeft
        · exact (hnoRight ⟨x, Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hx).1, hxRight⟩⟩).elim
      have hzLeftBlock : z ∈ leftBlock := by
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hz).2 with
          hzLeft | hzRight
        · exact hzLeft
        · exact (hnoRight ⟨z, Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hz).1, hzRight⟩⟩).elim
      have hxEndpoint := root_deep.lower_mem_cap_isSweepEndpoint
        hcapSubRoot hcapSet ⟨y, hy⟩
        (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
      have hzEndpoint := root_deep.lower_mem_cap_isSweepEndpoint
        hcapSubRoot hcapSet ⟨y, hy⟩
        (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz).2
      have hxLeftEndpoint :
          HasDeepBelowSplit.IsLeftSweepEndpoint cap x := by
        rcases hxEndpoint with hxLeftEndpoint | hxRightEndpoint
        · exact hxLeftEndpoint
        · have hyx := hxRightEndpoint y hyCap
          have hxVal := (Finset.mem_filter.mp hxLeftBlock).2
          have hyVal := (Finset.mem_filter.mp hyMiddle).2.1
          omega
      have hzLeftEndpoint :
          HasDeepBelowSplit.IsLeftSweepEndpoint cap z := by
        rcases hzEndpoint with hzLeftEndpoint | hzRightEndpoint
        · exact hzLeftEndpoint
        · have hyz := hzRightEndpoint y hyCap
          have hzVal := (Finset.mem_filter.mp hzLeftBlock).2
          have hyVal := (Finset.mem_filter.mp hyMiddle).2.1
          omega
      exact le_antisymm
        (hxLeftEndpoint z (Finset.mem_inter.mp hz).1)
        (hzLeftEndpoint x (Finset.mem_inter.mp hx).1)
    omega

/-- All four-cap sweep intervals in the construction straddle the omitted
vertex `q = 11`. -/
theorem every_fourCap_straddles_q
    (cap : Finset (Fin 33))
    (hcap : cap ∈ capWitnesses color support 4) :
    (finsetSweepInterval cap
      (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val := by
  obtain ⟨⟨a, ha⟩, ⟨d, hd⟩⟩ := fourCap_meets_outer_blocks cap hcap
  have haCap : a ∈ cap := (Finset.mem_inter.mp ha).1
  have haVal : a.val < 11 :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2
  have hdCap : d ∈ cap := (Finset.mem_inter.mp hd).1
  have hdVal : 23 ≤ d.val :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hd).2).2
  let hnonempty := capWitness_nonempty_of_mem (by omega) hcap
  constructor
  · change (cap.min' hnonempty).val < q.val
    have hmin := Finset.min'_le cap a haCap
    simp only [q]
    omega
  · change q.val ≤ (cap.max' hnonempty).val
    have hmax := Finset.le_max' cap d hdCap
    simp only [q]
    omega

/-- Exact Lean refutation of the proposed `32/23` strict-span recurrence.
The counterexample is decomposable, every 23-subset contains a four-cap, and
all four-cap spans share a cut; finite minimum width therefore rules out
strict descent for every cap. -/
theorem not_denseFourCapStrictSpanDescent32_23 :
    ¬DenseFourCapStrictSpanDescent32_23 := by
  intro hdescent
  obtain ⟨tree⟩ :=
    DecompositionTree.exists_of_isDecomposableOn decomposable_support
  exact false_of_denseFourCapStrictSpanDescent32_23
    hdescent tree support_card dense_fourCaps every_fourCap_straddles_q

end DenseSpanCounterexample

end ErdosSzekeres

end
