module

public import ErdosSzekeres.StructuralChargingResidueTransitions

@[expose] public section

/-!
# Crossing splits in the strong-six packing

At the balanced sharp boundary, every six-vertex deletion leaves a strong six.
When neither eleven-point side contains an internal strong six, every such
witness crosses the cut. This file classifies its five possible side splits
and identifies the two extreme splits with strong-five residues.
-/

namespace ErdosSzekeres

/-- A strong six-set whose intersections with the two sides have prescribed
cardinalities. -/
def HasCrossingStrongSixSplit {n : ℕ} (χ : TripleColoring n)
    (left right : Finset (Fin n)) (a b : ℕ) : Prop :=
  ∃ polygon : Finset (Fin n), polygon ⊆ left ∪ right ∧ polygon.card = 6 ∧
    IsStrongPolygonSet χ polygon ∧
    (polygon ∩ left).card = a ∧ (polygon ∩ right).card = b

/-- A set contained in two disjoint sides is the union of its two side
intersections. -/
theorem union_side_intersections_eq
    {α : Type*} [DecidableEq α] {left right polygon : Finset α}
    (hsub : polygon ⊆ left ∪ right) :
    (polygon ∩ left) ∪ (polygon ∩ right) = polygon := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).1
    · exact (Finset.mem_inter.mp hx).1
  · intro hx
    rcases Finset.mem_union.mp (hsub hx) with hxLeft | hxRight
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxLeft⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxRight⟩)

/-- Intersections of one set with two disjoint sides remain disjoint. -/
theorem side_intersections_disjoint
    {α : Type*} [DecidableEq α] {left right polygon : Finset α}
    (hdisjoint : Disjoint left right) :
    Disjoint (polygon ∩ left) (polygon ∩ right) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxLeft hxRight
  exact Finset.disjoint_left.mp hdisjoint
    (Finset.mem_inter.mp hxLeft).2 (Finset.mem_inter.mp hxRight).2

/-- In the balanced no-internal-strong-six branch, every packed witness left
inside the ambient set has exactly one of the five proper crossing splits. -/
theorem strongSix_has_proper_crossing_split
    {n : ℕ} {χ : TripleColoring n} {left right polygon : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hpolygonSub : polygon ⊆ left ∪ right) (hpolygonCard : polygon.card = 6)
    (hpolygonStrong : IsStrongPolygonSet χ polygon)
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6) :
    ((polygon ∩ left).card = 1 ∧ (polygon ∩ right).card = 5) ∨
    ((polygon ∩ left).card = 2 ∧ (polygon ∩ right).card = 4) ∨
    ((polygon ∩ left).card = 3 ∧ (polygon ∩ right).card = 3) ∨
    ((polygon ∩ left).card = 4 ∧ (polygon ∩ right).card = 2) ∨
    ((polygon ∩ left).card = 5 ∧ (polygon ∩ right).card = 1) := by
  have hleftPos : 0 < (polygon ∩ left).card := by
    by_contra hnot
    have hzero : (polygon ∩ left).card = 0 := by omega
    have hinterEmpty : polygon ∩ left = ∅ := Finset.card_eq_zero.mp hzero
    have hpolygonRight : polygon ⊆ right := by
      intro x hx
      rcases Finset.mem_union.mp (hpolygonSub hx) with hxLeft | hxRight
      · have hxInter : x ∈ polygon ∩ left := Finset.mem_inter.mpr ⟨hx, hxLeft⟩
        rw [hinterEmpty] at hxInter
        simp at hxInter
      · exact hxRight
    exact hnoRightStrong ⟨polygon, hpolygonRight, hpolygonCard, hpolygonStrong⟩
  have hrightPos : 0 < (polygon ∩ right).card := by
    by_contra hnot
    have hzero : (polygon ∩ right).card = 0 := by omega
    have hinterEmpty : polygon ∩ right = ∅ := Finset.card_eq_zero.mp hzero
    have hpolygonLeft : polygon ⊆ left := by
      intro x hx
      rcases Finset.mem_union.mp (hpolygonSub hx) with hxLeft | hxRight
      · exact hxLeft
      · have hxInter : x ∈ polygon ∩ right := Finset.mem_inter.mpr ⟨hx, hxRight⟩
        rw [hinterEmpty] at hxInter
        simp at hxInter
    exact hnoLeftStrong ⟨polygon, hpolygonLeft, hpolygonCard, hpolygonStrong⟩
  have hcardSum : (polygon ∩ left).card + (polygon ∩ right).card = 6 := by
    calc
      (polygon ∩ left).card + (polygon ∩ right).card =
          ((polygon ∩ left) ∪ (polygon ∩ right)).card :=
        (Finset.card_union_of_disjoint
          (side_intersections_disjoint hdisjoint)).symm
      _ = polygon.card := congrArg Finset.card
        (union_side_intersections_eq hpolygonSub)
      _ = 6 := hpolygonCard
  omega

/-- In the balanced no-internal-strong-six branch, every packed witness left
after a prescribed six-deletion has exactly one of the five proper crossing
splits. -/
theorem packedStrongSix_has_proper_crossing_split_avoiding
    {n : ℕ} {χ : TripleColoring n} {left right deleted : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hdeletedSub : deleted ⊆ left ∪ right) (hdeletedCard : deleted.card = 6) :
    ∃ polygon : Finset (Fin n), polygon ⊆ (left ∪ right) \ deleted ∧
      polygon.card = 6 ∧ IsStrongPolygonSet χ polygon ∧
      (((polygon ∩ left).card = 1 ∧ (polygon ∩ right).card = 5) ∨
       ((polygon ∩ left).card = 2 ∧ (polygon ∩ right).card = 4) ∨
       ((polygon ∩ left).card = 3 ∧ (polygon ∩ right).card = 3) ∨
       ((polygon ∩ left).card = 4 ∧ (polygon ∩ right).card = 2) ∨
       ((polygon ∩ left).card = 5 ∧ (polygon ∩ right).card = 1)) := by
  obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ :=
    hpacking deleted hdeletedSub hdeletedCard
  exact ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong,
    strongSix_has_proper_crossing_split hdisjoint
      (hpolygonSub.trans Finset.sdiff_subset) hpolygonCard hpolygonStrong
      hnoLeftStrong hnoRightStrong⟩

/-- An explicit `1+5` strong six supplies a strong-five residue at its unique
left vertex, which remains a member of the original polygon. -/
theorem one_five_strongSix_gives_left_strongResidue_at
    {n : ℕ} {χ : TripleColoring n} {left right polygon : Finset (Fin n)}
    (hpolygonSub : polygon ⊆ left ∪ right)
    (hpolygonStrong : IsStrongPolygonSet χ polygon)
    (hleftCard : (polygon ∩ left).card = 1)
    (hrightCard : (polygon ∩ right).card = 5) :
    ∃ q, q ∈ polygon ∧ q ∈ left ∧ HasAdjoinedStrongSixResidue χ right q := by
  obtain ⟨q, hleftEq⟩ := Finset.card_eq_one.mp hleftCard
  let base := polygon ∩ right
  have hdecomp := union_side_intersections_eq hpolygonSub
  have hinsert : insert q base = polygon := by
    simpa [base, hleftEq] using hdecomp
  have hqInter : q ∈ polygon ∩ left := by simp [hleftEq]
  refine ⟨q, (Finset.mem_inter.mp hqInter).1,
    (Finset.mem_inter.mp hqInter).2, base,
    Finset.inter_subset_right, ?_, ?_⟩
  · exact hrightCard
  · rw [hinsert]
    exact hpolygonStrong

/-- A `1+5` crossing strong six supplies a strong-five residue on the right
for its unique left vertex. -/
theorem one_five_crossingStrongSix_gives_left_strongResidue
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hsplit : HasCrossingStrongSixSplit χ left right 1 5) :
    ∃ q ∈ left, HasAdjoinedStrongSixResidue χ right q := by
  obtain ⟨polygon, hpolygonSub, _hpolygonCard, hpolygonStrong,
    hleftCard, hrightCard⟩ := hsplit
  obtain ⟨q, _hqPolygon, hqLeft, hresidue⟩ :=
    one_five_strongSix_gives_left_strongResidue_at
      hpolygonSub hpolygonStrong hleftCard hrightCard
  exact ⟨q, hqLeft, hresidue⟩

/-- A `5+1` crossing strong six supplies a strong-five residue on the left
for its unique right vertex. -/
theorem five_one_crossingStrongSix_gives_right_strongResidue
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hsplit : HasCrossingStrongSixSplit χ left right 5 1) :
    ∃ q ∈ right, HasAdjoinedStrongSixResidue χ left q := by
  obtain ⟨polygon, hpolygonSub, _hpolygonCard, hpolygonStrong,
    hleftCard, hrightCard⟩ := hsplit
  obtain ⟨q, hrightEq⟩ := Finset.card_eq_one.mp hrightCard
  let base := polygon ∩ left
  have hdecomp := union_side_intersections_eq hpolygonSub
  have hinsert : insert q base = polygon := by
    rw [Finset.union_comm] at hdecomp
    simpa [base, hrightEq] using hdecomp
  have hqInter : q ∈ polygon ∩ right := by simp [hrightEq]
  refine ⟨q, (Finset.mem_inter.mp hqInter).2, base,
    Finset.inter_subset_right, ?_, ?_⟩
  · exact hleftCard
  · rw [hinsert]
    exact hpolygonStrong

/-- An explicit `5+1` strong six supplies a strong-five residue at its unique
right vertex, which remains a member of the original polygon. -/
theorem five_one_strongSix_gives_right_strongResidue_at
    {n : ℕ} {χ : TripleColoring n} {left right polygon : Finset (Fin n)}
    (hpolygonSub : polygon ⊆ left ∪ right)
    (hpolygonStrong : IsStrongPolygonSet χ polygon)
    (hleftCard : (polygon ∩ left).card = 5)
    (hrightCard : (polygon ∩ right).card = 1) :
    ∃ q, q ∈ polygon ∧ q ∈ right ∧ HasAdjoinedStrongSixResidue χ left q := by
  have hmirrorSub : polygon ⊆ right ∪ left := by
    simpa [Finset.union_comm] using hpolygonSub
  obtain ⟨q, hqPolygon, hqRight, hresidue⟩ :=
    one_five_strongSix_gives_left_strongResidue_at
      hmirrorSub hpolygonStrong hrightCard hleftCard
  exact ⟨q, hqPolygon, hqRight, hresidue⟩

/-- Conversely, a left vertex with a strong-five residue on the right gives
a `1+5` crossing strong six. -/
theorem left_strongResidue_gives_one_five_crossingStrongSix
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)} {q : Fin n}
    (hdisjoint : Disjoint left right) (hqLeft : q ∈ left)
    (hresidue : HasAdjoinedStrongSixResidue χ right q) :
    HasCrossingStrongSixSplit χ left right 1 5 := by
  obtain ⟨base, hbaseSub, hbaseCard, hstrong⟩ := hresidue
  have hqRight : q ∉ right := fun hqRight ↦
    Finset.disjoint_left.mp hdisjoint hqLeft hqRight
  have hqBase : q ∉ base := fun hqBase ↦ hqRight (hbaseSub hqBase)
  have hleftInter : insert q base ∩ left = {q} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_insert.mp (Finset.mem_inter.mp hx).1 with rfl | hxBase
      · simp
      · exact (Finset.disjoint_left.mp hdisjoint (Finset.mem_inter.mp hx).2
          (hbaseSub hxBase)).elim
    · intro hx
      have hxq := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_self q base, hqLeft⟩
  have hrightInter : insert q base ∩ right = base := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_insert.mp (Finset.mem_inter.mp hx).1 with rfl | hxBase
      · exact (hqRight (Finset.mem_inter.mp hx).2).elim
      · exact hxBase
    · intro hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hx, hbaseSub hx⟩
  refine ⟨insert q base, ?_, ?_, hstrong, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxBase
    · exact Finset.mem_union_left right hqLeft
    · exact Finset.mem_union_right left (hbaseSub hxBase)
  · simp [Finset.card_insert_of_notMem, hqBase, hbaseCard]
  · simp [hleftInter]
  · simpa [hrightInter] using hbaseCard

/-- Conversely, a right vertex with a strong-five residue on the left gives
a `5+1` crossing strong six. -/
theorem right_strongResidue_gives_five_one_crossingStrongSix
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)} {q : Fin n}
    (hdisjoint : Disjoint left right) (hqRight : q ∈ right)
    (hresidue : HasAdjoinedStrongSixResidue χ left q) :
    HasCrossingStrongSixSplit χ left right 5 1 := by
  have hmirror : HasCrossingStrongSixSplit χ right left 1 5 :=
    left_strongResidue_gives_one_five_crossingStrongSix
      hdisjoint.symm hqRight hresidue
  obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong,
    hrightCard, hleftCard⟩ := hmirror
  exact ⟨polygon, by simpa [Finset.union_comm] using hpolygonSub,
    hpolygonCard, hpolygonStrong, hleftCard, hrightCard⟩

/-- Extreme `1+5` packed witnesses are equivalent to left vertices carrying
strong-five residues on the right. -/
theorem one_five_crossingStrongSix_iff_left_strongResidue
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right) :
    HasCrossingStrongSixSplit χ left right 1 5 ↔
      ∃ q ∈ left, HasAdjoinedStrongSixResidue χ right q := by
  constructor
  · exact one_five_crossingStrongSix_gives_left_strongResidue
  · rintro ⟨q, hqLeft, hresidue⟩
    exact left_strongResidue_gives_one_five_crossingStrongSix
      hdisjoint hqLeft hresidue

/-- Extreme `5+1` packed witnesses are equivalent to right vertices carrying
strong-five residues on the left. -/
theorem five_one_crossingStrongSix_iff_right_strongResidue
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right) :
    HasCrossingStrongSixSplit χ left right 5 1 ↔
      ∃ q ∈ right, HasAdjoinedStrongSixResidue χ left q := by
  constructor
  · exact five_one_crossingStrongSix_gives_right_strongResidue
  · rintro ⟨q, hqRight, hresidue⟩
    exact right_strongResidue_gives_five_one_crossingStrongSix
      hdisjoint hqRight hresidue

/-- Vertices in one set which carry a strong-five residue in another set. -/
noncomputable def StrongResidueCarriersInto {n : ℕ} (χ : TripleColoring n)
    (external side : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact external.filter fun q ↦ HasAdjoinedStrongSixResidue χ side q

/-- Left-side vertices which carry a strong-five residue on the right. -/
noncomputable def LeftStrongResidueCarriers {n : ℕ} (χ : TripleColoring n)
    (left right : Finset (Fin n)) : Finset (Fin n) :=
  StrongResidueCarriersInto χ left right

/-- Right-side vertices which carry a strong-five residue on the left. -/
noncomputable def RightStrongResidueCarriers {n : ℕ} (χ : TripleColoring n)
    (left right : Finset (Fin n)) : Finset (Fin n) :=
  StrongResidueCarriersInto χ right left

/-- All vertices which occur as the singleton side of an extreme crossing
strong six. -/
noncomputable def StrongResidueCarriers {n : ℕ} (χ : TripleColoring n)
    (left right : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact LeftStrongResidueCarriers χ left right ∪
    RightStrongResidueCarriers χ left right

@[simp] theorem mem_strongResidueCarriersInto_iff
    {n : ℕ} {χ : TripleColoring n} {external side : Finset (Fin n)} {q : Fin n} :
    q ∈ StrongResidueCarriersInto χ external side ↔
      q ∈ external ∧ HasAdjoinedStrongSixResidue χ side q := by
  classical
  simp [StrongResidueCarriersInto]

@[simp] theorem mem_leftStrongResidueCarriers_iff
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)} {q : Fin n} :
    q ∈ LeftStrongResidueCarriers χ left right ↔
      q ∈ left ∧ HasAdjoinedStrongSixResidue χ right q := by
  exact mem_strongResidueCarriersInto_iff

@[simp] theorem mem_rightStrongResidueCarriers_iff
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)} {q : Fin n} :
    q ∈ RightStrongResidueCarriers χ left right ↔
      q ∈ right ∧ HasAdjoinedStrongSixResidue χ left q := by
  exact mem_strongResidueCarriersInto_iff

@[simp] theorem mem_strongResidueCarriers_iff
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)} {q : Fin n} :
    q ∈ StrongResidueCarriers χ left right ↔
      (q ∈ left ∧ HasAdjoinedStrongSixResidue χ right q) ∨
      (q ∈ right ∧ HasAdjoinedStrongSixResidue χ left q) := by
  classical
  simp [StrongResidueCarriers]

/-- Three ordered external vertices with strong-five residues in one
eleven-set, two of whose residue bases share at least two vertices. -/
def HasThreeStrongResiduesWithPairOverlap {n : ℕ} (χ : TripleColoring n)
    (external side : Finset (Fin n)) : Prop :=
  ∃ q r s, q ∈ external ∧ r ∈ external ∧ s ∈ external ∧ q < r ∧ r < s ∧
    ∃ a b c, a ⊆ side ∧ b ⊆ side ∧ c ⊆ side ∧
      a.card = 5 ∧ b.card = 5 ∧ c.card = 5 ∧
      IsStrongPolygonSet χ (insert q a) ∧
      IsStrongPolygonSet χ (insert r b) ∧
      IsStrongPolygonSet χ (insert s c) ∧
      (2 ≤ (a ∩ b).card ∨ 2 ≤ (a ∩ c).card ∨ 2 ≤ (b ∩ c).card)

/-- Three strong-residue carrier vertices into an eleven-set have residue
bases with a pair overlap. -/
theorem three_strongResidueCarriersInto_have_pairOverlap
    {n : ℕ} {χ : TripleColoring n} {external side : Finset (Fin n)}
    (hsideCard : side.card = 11)
    (hthree : 3 ≤ (StrongResidueCarriersInto χ external side).card) :
    HasThreeStrongResiduesWithPairOverlap χ external side := by
  classical
  obtain ⟨chosen, hchosenSub, hchosenCard⟩ :=
    Finset.exists_subset_card_eq hthree
  let e : Fin 3 ↪o Fin n := chosen.orderEmbOfFin hchosenCard
  have heChosen (i : Fin 3) : e i ∈ chosen :=
    chosen.orderEmbOfFin_mem hchosenCard i
  have heCarrier (i : Fin 3) :
      e i ∈ StrongResidueCarriersInto χ external side :=
    hchosenSub (heChosen i)
  have heExternal (i : Fin 3) : e i ∈ external :=
    (mem_strongResidueCarriersInto_iff.mp (heCarrier i)).1
  have heResidue (i : Fin 3) : HasAdjoinedStrongSixResidue χ side (e i) :=
    (mem_strongResidueCarriersInto_iff.mp (heCarrier i)).2
  obtain ⟨a, haSub, haCard, haStrong⟩ := heResidue 0
  obtain ⟨b, hbSub, hbCard, hbStrong⟩ := heResidue 1
  obtain ⟨c, hcSub, hcCard, hcStrong⟩ := heResidue 2
  have hoverlap := three_five_subsets_of_eleven_pair_overlap hsideCard
    haSub hbSub hcSub haCard hbCard hcCard
  exact ⟨e 0, e 1, e 2, heExternal 0, heExternal 1, heExternal 2,
    e.strictMono (by decide), e.strictMono (by decide), a, b, c,
    haSub, hbSub, hcSub, haCard, hbCard, hcCard,
    haStrong, hbStrong, hcStrong, hoverlap⟩

/-- If all three middle crossing splits are absent, the deletion packing
forces at least seven extreme-split carrier vertices. -/
theorem seven_strongResidueCarriers_of_packing_no_middle_splits
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hleftCard : left.card = 11) (hrightCard : right.card = 11)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hnoTwoFour : ¬HasCrossingStrongSixSplit χ left right 2 4)
    (hnoThreeThree : ¬HasCrossingStrongSixSplit χ left right 3 3)
    (hnoFourTwo : ¬HasCrossingStrongSixSplit χ left right 4 2) :
    7 ≤ (StrongResidueCarriers χ left right).card := by
  classical
  let carriers := StrongResidueCarriers χ left right
  change 7 ≤ carriers.card
  have hcarriersSub : carriers ⊆ left ∪ right := by
    intro q hq
    rcases mem_strongResidueCarriers_iff.mp hq with hqLeft | hqRight
    · exact Finset.mem_union_left right hqLeft.1
    · exact Finset.mem_union_right left hqRight.1
  have hambientCard : 6 ≤ (left ∪ right).card := by
    rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard]
    omega
  by_contra hnot
  have hcarriersCard : carriers.card ≤ 6 := by omega
  obtain ⟨deleted, hcarriersDeleted, hdeletedSub, hdeletedCard⟩ :=
    Finset.exists_subsuperset_card_eq hcarriersSub hcarriersCard hambientCard
  obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong, hsplit⟩ :=
    packedStrongSix_has_proper_crossing_split_avoiding hdisjoint hpacking
      hnoLeftStrong hnoRightStrong hdeletedSub hdeletedCard
  have hpolygonAmbient : polygon ⊆ left ∪ right :=
    hpolygonSub.trans Finset.sdiff_subset
  rcases hsplit with hsplit | hsplit | hsplit | hsplit | hsplit
  · obtain ⟨q, hqPolygon, hqLeft, hresidue⟩ :=
      one_five_strongSix_gives_left_strongResidue_at hpolygonAmbient
        hpolygonStrong hsplit.1 hsplit.2
    have hqCarrier : q ∈ carriers := by
      exact mem_strongResidueCarriers_iff.mpr (Or.inl ⟨hqLeft, hresidue⟩)
    exact (Finset.mem_sdiff.mp (hpolygonSub hqPolygon)).2
      (hcarriersDeleted hqCarrier)
  · exact hnoTwoFour
      ⟨polygon, hpolygonAmbient, hpolygonCard, hpolygonStrong,
        hsplit.1, hsplit.2⟩
  · exact hnoThreeThree
      ⟨polygon, hpolygonAmbient, hpolygonCard, hpolygonStrong,
        hsplit.1, hsplit.2⟩
  · exact hnoFourTwo
      ⟨polygon, hpolygonAmbient, hpolygonCard, hpolygonStrong,
        hsplit.1, hsplit.2⟩
  · obtain ⟨q, hqPolygon, hqRight, hresidue⟩ :=
      five_one_strongSix_gives_right_strongResidue_at hpolygonAmbient
        hpolygonStrong hsplit.1 hsplit.2
    have hqCarrier : q ∈ carriers := by
      exact mem_strongResidueCarriers_iff.mpr (Or.inr ⟨hqRight, hresidue⟩)
    exact (Finset.mem_sdiff.mp (hpolygonSub hqPolygon)).2
      (hcarriersDeleted hqCarrier)

/-- Seven total extreme-split carriers put at least four carriers on one side
of the balanced cut. -/
theorem four_strongResidueCarriers_on_one_side_of_seven
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hseven : 7 ≤ (StrongResidueCarriers χ left right).card) :
    4 ≤ (LeftStrongResidueCarriers χ left right).card ∨
      4 ≤ (RightStrongResidueCarriers χ left right).card := by
  classical
  have hleftSub : LeftStrongResidueCarriers χ left right ⊆ left :=
    fun _ hq ↦ (mem_leftStrongResidueCarriers_iff.mp hq).1
  have hrightSub : RightStrongResidueCarriers χ left right ⊆ right :=
    fun _ hq ↦ (mem_rightStrongResidueCarriers_iff.mp hq).1
  have hcarrierDisjoint :
      Disjoint (LeftStrongResidueCarriers χ left right)
        (RightStrongResidueCarriers χ left right) :=
    hdisjoint.mono hleftSub hrightSub
  have hcarrierEq : StrongResidueCarriers χ left right =
      LeftStrongResidueCarriers χ left right ∪
        RightStrongResidueCarriers χ left right := by
    rfl
  rw [hcarrierEq, Finset.card_union_of_disjoint hcarrierDisjoint] at hseven
  omega

/-- Conditional packing-to-residue bridge: after excluding middle crossing
splits, at least four vertices on one side carry strong-five residues. -/
theorem four_strongResidueCarriers_on_one_side_of_packing_no_middle_splits
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hleftCard : left.card = 11) (hrightCard : right.card = 11)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hnoTwoFour : ¬HasCrossingStrongSixSplit χ left right 2 4)
    (hnoThreeThree : ¬HasCrossingStrongSixSplit χ left right 3 3)
    (hnoFourTwo : ¬HasCrossingStrongSixSplit χ left right 4 2) :
    4 ≤ (LeftStrongResidueCarriers χ left right).card ∨
      4 ≤ (RightStrongResidueCarriers χ left right).card :=
  four_strongResidueCarriers_on_one_side_of_seven hdisjoint
    (seven_strongResidueCarriers_of_packing_no_middle_splits hdisjoint
      hleftCard hrightCard hpacking hnoLeftStrong hnoRightStrong
      hnoTwoFour hnoThreeThree hnoFourTwo)

/-- With middle crossing splits excluded, the strong-six packing activates
the three-residue pair-overlap theorem on one side of the balanced cut. -/
theorem packing_no_middle_splits_gives_three_residues_with_pairOverlap
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hleftCard : left.card = 11) (hrightCard : right.card = 11)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hnoTwoFour : ¬HasCrossingStrongSixSplit χ left right 2 4)
    (hnoThreeThree : ¬HasCrossingStrongSixSplit χ left right 3 3)
    (hnoFourTwo : ¬HasCrossingStrongSixSplit χ left right 4 2) :
    HasThreeStrongResiduesWithPairOverlap χ left right ∨
      HasThreeStrongResiduesWithPairOverlap χ right left := by
  rcases four_strongResidueCarriers_on_one_side_of_packing_no_middle_splits
      hdisjoint hleftCard hrightCard hpacking hnoLeftStrong hnoRightStrong
      hnoTwoFour hnoThreeThree hnoFourTwo with hleft | hright
  · apply Or.inl
    apply three_strongResidueCarriersInto_have_pairOverlap hrightCard
    change 3 ≤ (LeftStrongResidueCarriers χ left right).card
    omega
  · apply Or.inr
    apply three_strongResidueCarriersInto_have_pairOverlap hleftCard
    change 3 ≤ (RightStrongResidueCarriers χ left right).card
    omega

end ErdosSzekeres

end
