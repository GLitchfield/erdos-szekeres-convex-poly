module

public import ErdosSzekeres.StructuralChargingPackingResidues
public import ErdosSzekeres.StructuralChargingWitnessBranchesPacked
public import ErdosSzekeres.StructuralChargingMiddleSplits

@[expose] public section

/-!
# Exact balanced state-567 exhaustion

This file freezes the common `11+11` counterexample context and packages the
existing crossing-split/residue machinery as an exact five-way disjunction.
The five terminal color contradictions remain independent obligations.
-/

namespace ErdosSzekeres

/-- The full open balanced counterexample context at state `(5,6,7)`. -/
def PackedElevenElevenOpen567 {n : ℕ} (χ : TripleColoring n)
    (left right : Finset (Fin n)) : Prop :=
  Disjoint left right ∧
    (∀ x ∈ left, ∀ y ∈ right, x < y) ∧
    left.card = 11 ∧ right.card = 11 ∧
    ¬ContainsCapSet χ left 4 ∧
    ¬ContainsCapSet χ right 4 ∧
    OneChangeOn χ (left ∪ right) ∧
    ¬ContainsCapSet χ (left ∪ right) 5 ∧
    ¬ContainsCupSet χ (left ∪ right) 6 ∧
    ¬ContainsStrongPolygonSet χ (left ∪ right) 7 ∧
    StrongSixAvoidsEverySix χ (left ∪ right) ∧
    ¬ContainsStrongPolygonSet χ left 6 ∧
    ¬ContainsStrongPolygonSet χ right 6

/-- The exact five terminal classes left by balanced deletion packing. -/
def BalancedFiveWay567 {n : ℕ} (χ : TripleColoring n)
    (left right : Finset (Fin n)) : Prop :=
  HasCrossingStrongSixSplit χ left right 2 4 ∨
    HasCrossingStrongSixSplit χ left right 3 3 ∨
    HasCrossingStrongSixSplit χ left right 4 2 ∨
    HasThreeStrongResiduesWithPairOverlap χ left right ∨
    HasThreeStrongResiduesWithPairOverlap χ right left

/-- Existing proper-split and residue theorems give a mechanical exhaustion
of every balanced open counterexample by the five terminal classes. -/
theorem PackedElevenElevenOpen567.has_fiveWay
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hopen : PackedElevenElevenOpen567 χ left right) :
    BalancedFiveWay567 χ left right := by
  rcases hopen with ⟨hdisjoint, _horder, hleftCard, hrightCard,
    _hleftCap, _hrightCap, _hone, _hnoCap, _hnoCup, _hnoStrong,
    hpacking, hnoLeftStrong, hnoRightStrong⟩
  by_cases htwoFour : HasCrossingStrongSixSplit χ left right 2 4
  · exact Or.inl htwoFour
  by_cases hthreeThree : HasCrossingStrongSixSplit χ left right 3 3
  · exact Or.inr (Or.inl hthreeThree)
  by_cases hfourTwo : HasCrossingStrongSixSplit χ left right 4 2
  · exact Or.inr (Or.inr (Or.inl hfourTwo))
  exact Or.inr (Or.inr (Or.inr
    (packing_no_middle_splits_gives_three_residues_with_pairOverlap
      hdisjoint hleftCard hrightCard hpacking hnoLeftStrong hnoRightStrong
      htwoFour hthreeThree hfourTwo)))

/-- A collective family of `2+4` strong sixes with no two-point transversal,
after avoiding every extreme residue carrier. -/
def CleanTwoFourAvoidsEveryTwo567 {n : ℕ} (χ : TripleColoring n)
    (left right : Finset (Fin n)) : Prop :=
  ∀ blocked : Finset (Fin n),
    blocked ⊆ left ∪ right → blocked.card ≤ 2 →
      ∃ polygon : Finset (Fin n),
        polygon ⊆ (left ∪ right) \ blocked ∧
        Disjoint polygon (StrongResidueCarriers χ left right) ∧
        polygon.card = 6 ∧ IsStrongPolygonSet χ polygon ∧
        (polygon ∩ left).card = 2 ∧ (polygon ∩ right).card = 4

/-- One member of the collective clean `2+4` family. -/
def IsCleanTwoFourWitness567 {n : ℕ} (χ : TripleColoring n)
    (left right polygon : Finset (Fin n)) : Prop :=
  polygon ⊆ left ∪ right ∧
    Disjoint polygon (StrongResidueCarriers χ left right) ∧
    polygon.card = 6 ∧ IsStrongPolygonSet χ polygon ∧
    (polygon ∩ left).card = 2 ∧ (polygon ∩ right).card = 4

/-- A family with no two-point transversal contains three distinct clean
`2+4` witnesses. -/
theorem CleanTwoFourAvoidsEveryTwo567.exists_three_distinct
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hclean : CleanTwoFourAvoidsEveryTwo567 χ left right) :
    ∃ first second third : Finset (Fin n),
      IsCleanTwoFourWitness567 χ left right first ∧
      IsCleanTwoFourWitness567 χ left right second ∧
      IsCleanTwoFourWitness567 χ left right third ∧
      first ≠ second ∧ first ≠ third ∧ second ≠ third := by
  obtain ⟨first, hfirstSub, hfirstCarriers, hfirstCard,
      hfirstStrong, hfirstLeft, hfirstRight⟩ :=
    hclean ∅ (by simp) (by simp)
  obtain ⟨q, hqFirst⟩ : first.Nonempty :=
    Finset.card_pos.mp (show 0 < first.card by omega)
  have hqAmbient : q ∈ left ∪ right :=
    (Finset.mem_sdiff.mp (hfirstSub hqFirst)).1
  obtain ⟨second, hsecondSub, hsecondCarriers, hsecondCard,
      hsecondStrong, hsecondLeft, hsecondRight⟩ :=
    hclean {q} (by simpa using hqAmbient) (by simp)
  obtain ⟨r, hrSecond⟩ : second.Nonempty :=
    Finset.card_pos.mp (show 0 < second.card by omega)
  have hrAmbient : r ∈ left ∪ right :=
    (Finset.mem_sdiff.mp (hsecondSub hrSecond)).1
  have hblockedSub : {q, r} ⊆ left ∪ right := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hqAmbient
    · exact hrAmbient
  obtain ⟨third, hthirdSub, hthirdCarriers, hthirdCard,
      hthirdStrong, hthirdLeft, hthirdRight⟩ :=
    hclean {q, r} hblockedSub Finset.card_le_two
  have hqNotSecond : q ∉ second := by
    intro hqSecond
    exact (Finset.mem_sdiff.mp (hsecondSub hqSecond)).2 (by simp)
  have hqNotThird : q ∉ third := by
    intro hqThird
    exact (Finset.mem_sdiff.mp (hthirdSub hqThird)).2 (by simp)
  have hrNotThird : r ∉ third := by
    intro hrThird
    exact (Finset.mem_sdiff.mp (hthirdSub hrThird)).2 (by simp)
  have hfirstNeSecond : first ≠ second := by
    intro heq
    exact hqNotSecond (heq ▸ hqFirst)
  have hfirstNeThird : first ≠ third := by
    intro heq
    exact hqNotThird (heq ▸ hqFirst)
  have hsecondNeThird : second ≠ third := by
    intro heq
    exact hrNotThird (heq ▸ hrSecond)
  exact ⟨first, second, third,
    ⟨hfirstSub.trans Finset.sdiff_subset, hfirstCarriers, hfirstCard,
      hfirstStrong, hfirstLeft, hfirstRight⟩,
    ⟨hsecondSub.trans Finset.sdiff_subset, hsecondCarriers, hsecondCard,
      hsecondStrong, hsecondLeft, hsecondRight⟩,
    ⟨hthirdSub.trans Finset.sdiff_subset, hthirdCarriers, hthirdCard,
      hthirdStrong, hthirdLeft, hthirdRight⟩,
    hfirstNeSecond, hfirstNeThird, hsecondNeThird⟩

/-- The nine possible middle words of a clean `2+4` witness: weight one or
two, excluding the pair whose two final internal positions are both right. -/
def StrongSixMiddleWordNinePattern {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) : Prop :=
  StrongSixMiddleWordWeightOneOrTwo χ polygon hcard ∧
    let e := polygon.orderEmbOfFin hcard
    ¬(χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.right)

/-- In an ordered `2+4` split, the last four vertices of the polygon's order
embedding lie in the right side. -/
theorem twoFour_orderEmb_final_mem_right
    {n : ℕ} {left right polygon : Finset (Fin n)}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left ∪ right)
    (hcard : polygon.card = 6)
    (hleftCard : (polygon ∩ left).card = 2)
    (i : Fin 6) (hi : 2 ≤ i) :
    polygon.orderEmbOfFin hcard i ∈ right := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (j : Fin 6) : e j ∈ polygon :=
    polygon.orderEmbOfFin_mem hcard j
  rcases Finset.mem_union.mp (hpolygonSub (heMem i)) with hiLeft | hiRight
  · have h0i : (0 : Fin 6) < i := by omega
    have h1i : (1 : Fin 6) < i := by omega
    have he0Left : e 0 ∈ left := by
      rcases Finset.mem_union.mp (hpolygonSub (heMem 0)) with h0Left | h0Right
      · exact h0Left
      · exact ((e.strictMono h0i).asymm
          (horder _ hiLeft _ h0Right)).elim
    have he1Left : e 1 ∈ left := by
      rcases Finset.mem_union.mp (hpolygonSub (heMem 1)) with h1Left | h1Right
      · exact h1Left
      · exact ((e.strictMono h1i).asymm
          (horder _ hiLeft _ h1Right)).elim
    let triple : Finset (Fin n) := {e 0, e 1, e i}
    have htripleSub : triple ⊆ polygon ∩ left := by
      intro x hx
      simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨heMem 0, he0Left⟩
      · exact Finset.mem_inter.mpr ⟨heMem 1, he1Left⟩
      · exact Finset.mem_inter.mpr ⟨heMem i, hiLeft⟩
    have htripleCard : triple.card = 3 := by
      simp [triple, ne_of_lt (e.strictMono (by decide : (0 : Fin 6) < 1)),
        ne_of_lt (e.strictMono h0i), ne_of_lt (e.strictMono h1i)]
    have hle := Finset.card_le_card htripleSub
    rw [htripleCard, hleftCard] at hle
    omega
  · exact hiRight

/-- Right-side cap-four avoidance excludes the only two-right middle word
whose right entries are both internal to the final four vertices. -/
theorem twoFour_final_right_middles_not_both_right
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left ∪ right)
    (hcard : polygon.card = 6)
    (hstrong : IsStrongPolygonSet χ polygon)
    (hleftCard : (polygon ∩ left).card = 2)
    (hnoRightCap : ¬ContainsCapSet χ right 4) :
    let e := polygon.orderEmbOfFin hcard
    ¬(χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.right) := by
  dsimp only
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (i : Fin 6) : e i ∈ polygon :=
    polygon.orderEmbOfFin_mem hcard i
  have hmiddle : IsMiddleDeterminedOn χ polygon :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
  have hcolor (i j k : Fin 6) (hij : i < j) (hjk : j < k)
      (hj0 : (0 : Fin 6) < j) (hj5 : j < (5 : Fin 6)) :
      χ ⟨e i, e j, e k, e.strictMono hij, e.strictMono hjk⟩ =
        χ ⟨e 0, e j, e 5, e.strictMono hj0, e.strictMono hj5⟩ :=
    hmiddle (e.strictMono hij) (e.strictMono hj0)
      (e.strictMono hjk) (e.strictMono hj5)
      (heMem i) (heMem 0) (heMem j) (heMem k) (heMem 5)
  rintro ⟨h3, h4⟩
  let g : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![e 2, e 3, e 4, e 5] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals exact e.strictMono (by decide))
  have hgSub : Finset.univ.image g ⊆ right := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · exact twoFour_orderEmb_final_mem_right horder hpolygonSub hcard
        hleftCard 2 (by decide)
    · exact twoFour_orderEmb_final_mem_right horder hpolygonSub hcard
        hleftCard 3 (by decide)
    · exact twoFour_orderEmb_final_mem_right horder hpolygonSub hcard
        hleftCard 4 (by decide)
    · exact twoFour_orderEmb_final_mem_right horder hpolygonSub hcard
        hleftCard 5 (by decide)
  apply hnoRightCap
  refine ⟨Finset.univ.image g, hgSub,
    by simpa using Finset.card_image_of_injective Finset.univ g.injective,
    FinsetPolygon.IsCap.image ?_⟩
  refine ⟨g.strictMono, ?_⟩
  intro i j k hij hjk
  fin_cases j
  · change i.val < 0 at hij
    omega
  · change i.val < 1 at hij
    change 1 < k.val at hjk
    have hi : i = 0 := by omega
    subst i
    have hk : k = 2 ∨ k = 3 := by omega
    rcases hk with rfl | rfl
    · simpa [g, e] using
        (hcolor 2 3 4 (by decide) (by decide) (by decide) (by decide)).trans h3
    · simpa [g, e] using
        (hcolor 2 3 5 (by decide) (by decide) (by decide) (by decide)).trans h3
  · change i.val < 2 at hij
    change 2 < k.val at hjk
    have hk : k = 3 := by omega
    subst k
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simpa [g, e] using
        (hcolor 2 4 5 (by decide) (by decide) (by decide) (by decide)).trans h4
    · simpa [g, e] using
        (hcolor 3 4 5 (by decide) (by decide) (by decide) (by decide)).trans h4
  · change 3 < k.val at hjk
    omega

/-- The exact nine-word normalization for one `2+4` witness under the ambient
state-567 exclusions. -/
theorem twoFour_strongSix_middleWordNinePattern
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left ∪ right)
    (hcard : polygon.card = 6)
    (hstrong : IsStrongPolygonSet χ polygon)
    (hleftCard : (polygon ∩ left).card = 2)
    (hnoRightCap : ¬ContainsCapSet χ right 4)
    (hnoAmbientCap : ¬ContainsCapSet χ (left ∪ right) 5)
    (hnoAmbientCup : ¬ContainsCupSet χ (left ∪ right) 6) :
    StrongSixMiddleWordNinePattern χ polygon hcard := by
  have hnoPolygonCap : ¬ContainsCapSet χ polygon 5 := by
    intro hcap
    exact hnoAmbientCap
      (FinsetPolygon.ContainsCapSet.mono hcap hpolygonSub)
  have hnoPolygonCup : ¬ContainsCupSet χ polygon 6 := by
    intro hcup
    exact hnoAmbientCup
      (FinsetPolygon.ContainsCupSet.mono hcup hpolygonSub)
  exact ⟨strongSix_middle_word_weight_one_or_two hcard hstrong
      hnoPolygonCap hnoPolygonCup,
    twoFour_final_right_middles_not_both_right horder hpolygonSub hcard
      hstrong hleftCard hnoRightCap⟩

/-- After the two residue-overlap directions and the `3+3` and `4+2`
classes are excluded, global deletion packing produces a clean `2+4` witness
avoiding any prescribed pair. -/
theorem packed_no_other_terminals_gives_clean_twoFour
    {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hleftCard : left.card = 11) (hrightCard : right.card = 11)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hnoThreeThree : ¬HasCrossingStrongSixSplit χ left right 3 3)
    (hnoFourTwo : ¬HasCrossingStrongSixSplit χ left right 4 2)
    (hnoLeftResidues :
      ¬HasThreeStrongResiduesWithPairOverlap χ left right)
    (hnoRightResidues :
      ¬HasThreeStrongResiduesWithPairOverlap χ right left) :
    CleanTwoFourAvoidsEveryTwo567 χ left right := by
  classical
  have hleftCarrierCard :
      (LeftStrongResidueCarriers χ left right).card ≤ 2 := by
    by_contra hnot
    apply hnoLeftResidues
    apply three_strongResidueCarriersInto_have_pairOverlap hrightCard
    change 3 ≤ (LeftStrongResidueCarriers χ left right).card
    omega
  have hrightCarrierCard :
      (RightStrongResidueCarriers χ left right).card ≤ 2 := by
    by_contra hnot
    apply hnoRightResidues
    apply three_strongResidueCarriersInto_have_pairOverlap hleftCard
    change 3 ≤ (RightStrongResidueCarriers χ left right).card
    omega
  let carriers := StrongResidueCarriers χ left right
  have hcarriersSub : carriers ⊆ left ∪ right := by
    intro q hq
    rcases mem_strongResidueCarriers_iff.mp hq with hqLeft | hqRight
    · exact Finset.mem_union_left right hqLeft.1
    · exact Finset.mem_union_right left hqRight.1
  have hcarriersCard : carriers.card ≤ 4 := by
    have hunionCard := Finset.card_union_le
      (LeftStrongResidueCarriers χ left right)
      (RightStrongResidueCarriers χ left right)
    change
      (LeftStrongResidueCarriers χ left right ∪
        RightStrongResidueCarriers χ left right).card ≤ 4
    omega
  intro blocked hblockedSub hblockedCard
  let forbidden := carriers ∪ blocked
  have hforbiddenSub : forbidden ⊆ left ∪ right :=
    Finset.union_subset hcarriersSub hblockedSub
  have hforbiddenCard : forbidden.card ≤ 6 := by
    have hunionCard := Finset.card_union_le carriers blocked
    change (carriers ∪ blocked).card ≤ 6
    omega
  have hambientCard : 6 ≤ (left ∪ right).card := by
    rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard]
    omega
  obtain ⟨deleted, hforbiddenDeleted, hdeletedSub, hdeletedCard⟩ :=
    Finset.exists_subsuperset_card_eq hforbiddenSub hforbiddenCard hambientCard
  obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong, hsplit⟩ :=
    packedStrongSix_has_proper_crossing_split_avoiding hdisjoint hpacking
      hnoLeftStrong hnoRightStrong hdeletedSub hdeletedCard
  have hpolygonAmbient : polygon ⊆ left ∪ right :=
    hpolygonSub.trans Finset.sdiff_subset
  have hpolygonBlocked : polygon ⊆ (left ∪ right) \ blocked := by
    intro x hxPolygon
    have hxAvoid := Finset.mem_sdiff.mp (hpolygonSub hxPolygon)
    exact Finset.mem_sdiff.mpr ⟨hxAvoid.1, fun hxBlocked ↦
      hxAvoid.2 (hforbiddenDeleted
        (Finset.mem_union_right carriers hxBlocked))⟩
  have hpolygonCarriers : Disjoint polygon carriers := by
    apply Finset.disjoint_left.mpr
    intro x hxPolygon hxCarrier
    have hxAvoid := Finset.mem_sdiff.mp (hpolygonSub hxPolygon)
    exact hxAvoid.2 (hforbiddenDeleted
      (Finset.mem_union_left blocked hxCarrier))
  rcases hsplit with hsplit | hsplit | hsplit | hsplit | hsplit
  · obtain ⟨q, hqPolygon, hqLeft, hresidue⟩ :=
      one_five_strongSix_gives_left_strongResidue_at hpolygonAmbient
        hpolygonStrong hsplit.1 hsplit.2
    have hqCarrier : q ∈ carriers :=
      mem_strongResidueCarriers_iff.mpr (Or.inl ⟨hqLeft, hresidue⟩)
    exact (Finset.disjoint_left.mp hpolygonCarriers hqPolygon hqCarrier).elim
  · exact ⟨polygon, hpolygonBlocked, hpolygonCarriers, hpolygonCard,
      hpolygonStrong, hsplit.1, hsplit.2⟩
  · exact (hnoThreeThree
      ⟨polygon, hpolygonAmbient, hpolygonCard, hpolygonStrong,
        hsplit.1, hsplit.2⟩).elim
  · exact (hnoFourTwo
      ⟨polygon, hpolygonAmbient, hpolygonCard, hpolygonStrong,
        hsplit.1, hsplit.2⟩).elim
  · obtain ⟨q, hqPolygon, hqRight, hresidue⟩ :=
      five_one_strongSix_gives_right_strongResidue_at hpolygonAmbient
        hpolygonStrong hsplit.1 hsplit.2
    have hqCarrier : q ∈ carriers :=
      mem_strongResidueCarriers_iff.mpr (Or.inr ⟨hqRight, hresidue⟩)
    exact (Finset.disjoint_left.mp hpolygonCarriers hqPolygon hqCarrier).elim

/-- Open contradiction contract for the central `3+3` balanced class. -/
def PackedBalancedThreeThreeImpossible567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    PackedElevenElevenOpen567 χ left right →
      HasCrossingStrongSixSplit χ left right 3 3 → False

/-- Open contradiction contract for the `4+2` balanced class. -/
def PackedBalancedFourTwoImpossible567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    PackedElevenElevenOpen567 χ left right →
      HasCrossingStrongSixSplit χ left right 4 2 → False

/-- Open contradiction contract for left vertices carrying three overlapping
strong-five residues into the right side. -/
def PackedBalancedLeftResiduesImpossible567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    PackedElevenElevenOpen567 χ left right →
      HasThreeStrongResiduesWithPairOverlap χ left right → False

/-- Open contradiction contract for the reverse residue direction. -/
def PackedBalancedRightResiduesImpossible567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    PackedElevenElevenOpen567 χ left right →
      HasThreeStrongResiduesWithPairOverlap χ right left → False

/-- The sharpened fifth terminal: the pair-transversal-free clean `2+4`
family is impossible in the full balanced context. -/
def CleanTwoFourEscapeFamilyImpossible567 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
    PackedElevenElevenOpen567 χ left right →
      CleanTwoFourAvoidsEveryTwo567 χ left right → False

/-- The four ordered preliminary terminal contradictions and the sharpened
clean-family contradiction imply the exact balanced state-567 obligation. -/
theorem packedElevenElevenForcesInternalStrongSix567_of_terminal_contracts
    (hthreeThree : PackedBalancedThreeThreeImpossible567)
    (hfourTwo : PackedBalancedFourTwoImpossible567)
    (hleftResidues : PackedBalancedLeftResiduesImpossible567)
    (hrightResidues : PackedBalancedRightResiduesImpossible567)
    (hcleanTwoFour : CleanTwoFourEscapeFamilyImpossible567) :
    PackedElevenElevenForcesInternalStrongSix567 := by
  intro n χ left right hdisjoint horder hleftCard hrightCard
    hleftCap hrightCap hone hnoCap hnoCup hnoStrong hpacking
  by_contra hnoInternal
  push Not at hnoInternal
  have hopen : PackedElevenElevenOpen567 χ left right :=
    ⟨hdisjoint, horder, hleftCard, hrightCard, hleftCap, hrightCap,
      hone, hnoCap, hnoCup, hnoStrong, hpacking,
      hnoInternal.1, hnoInternal.2⟩
  by_cases hleft : HasThreeStrongResiduesWithPairOverlap χ left right
  · exact hleftResidues hopen hleft
  by_cases hright : HasThreeStrongResiduesWithPairOverlap χ right left
  · exact hrightResidues hopen hright
  by_cases hthree : HasCrossingStrongSixSplit χ left right 3 3
  · exact hthreeThree hopen hthree
  by_cases hfour : HasCrossingStrongSixSplit χ left right 4 2
  · exact hfourTwo hopen hfour
  apply hcleanTwoFour hopen
  exact packed_no_other_terminals_gives_clean_twoFour hdisjoint
    hleftCard hrightCard hpacking hnoInternal.1 hnoInternal.2
    hthree hfour hleft hright

end ErdosSzekeres
