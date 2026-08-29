module

public import ErdosSzekeres.PredecessorHalfFin13
public import ErdosSzekeres.PredecessorMaximumSupport

@[expose] public section

/-!
# The exact maximum-support obstruction at fifteen points

The completed Fin13 theorem gives a strong-five-free seven-point support in
every strong-six-free one-change coloring on fifteen points.  Maximizing such
a support either reaches the required half size immediately or leaves an
exact seven-versus-eight obstruction.  In the latter case every exterior
vertex completes a strong five with a four-point anchor in the support.
-/

namespace ErdosSzekeres

/-- If fixed-size blocks have more total incidences than a uniform owner
capacity permits, some owner exceeds that capacity. -/
theorem exists_owner_degree_gt_of_total_gt_capacity
    {α : Type*} [DecidableEq α]
    (base family : Finset α) (block : α → Finset α)
    (blockCard capacity : ℕ)
    (hblockSub : ∀ item ∈ family, block item ⊆ base)
    (hblockCard : ∀ item ∈ family, (block item).card = blockCard)
    (hgt : capacity * base.card < blockCard * family.card) :
    ∃ owner ∈ base,
      capacity < (family.filter fun item ↦ owner ∈ block item).card := by
  classical
  by_contra hnone
  have hdegreeLe : ∀ owner ∈ base,
      (family.filter fun item ↦ owner ∈ block item).card ≤ capacity := by
    intro owner howner
    by_contra hlarge
    apply hnone
    exact ⟨owner, howner, by omega⟩
  have hdoubleCount :
      (∑ owner ∈ base,
        (family.filter fun item ↦ owner ∈ block item).card) =
      ∑ item ∈ family,
        (base.filter fun owner ↦ owner ∈ block item).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hfilter (item : α) (hitem : item ∈ family) :
      base.filter (fun owner ↦ owner ∈ block item) = block item := by
    ext owner
    simp only [Finset.mem_filter]
    constructor
    · exact fun howner ↦ howner.2
    · exact fun howner ↦ ⟨hblockSub item hitem howner, howner⟩
  have htotal :
      (∑ owner ∈ base,
        (family.filter fun item ↦ owner ∈ block item).card) =
      blockCard * family.card := by
    rw [hdoubleCount]
    calc
      (∑ item ∈ family,
          (base.filter fun owner ↦ owner ∈ block item).card) =
          ∑ item ∈ family, (block item).card := by
            apply Finset.sum_congr rfl
            intro item hitem
            rw [hfilter item hitem]
      _ = ∑ _item ∈ family, blockCard := by
        apply Finset.sum_congr rfl
        exact hblockCard
      _ = blockCard * family.card := by simp [Nat.mul_comm]
  have hupper :
      (∑ owner ∈ base,
        (family.filter fun item ↦ owner ∈ block item).card) ≤
      capacity * base.card := by
    calc
      (∑ owner ∈ base,
          (family.filter fun item ↦ owner ∈ block item).card) ≤
          ∑ _owner ∈ base, capacity := by
            apply Finset.sum_le_sum
            exact hdegreeLe
      _ = capacity * base.card := by simp [Nat.mul_comm]
  omega

/-- Eight four-point anchors in a seven-point support force one support
vertex to occur in at least five anchors. -/
theorem exists_fiveFoldOwner_of_seven_eight_fourAnchors
    {α : Type*} [DecidableEq α]
    (support exterior : Finset α) (anchor : α → Finset α)
    (hsupportCard : support.card = 7)
    (hexteriorCard : exterior.card = 8)
    (hanchorSub : ∀ vertex ∈ exterior, anchor vertex ⊆ support)
    (hanchorCard : ∀ vertex ∈ exterior, (anchor vertex).card = 4) :
    ∃ owner ∈ support,
      5 ≤ (exterior.filter fun vertex ↦ owner ∈ anchor vertex).card := by
  classical
  by_contra hnone
  have hdegreeLe : ∀ owner ∈ support,
      (exterior.filter fun vertex ↦ owner ∈ anchor vertex).card ≤ 4 := by
    intro owner howner
    by_contra hlarge
    apply hnone
    exact ⟨owner, howner, by omega⟩
  have hdoubleCount :
      (∑ owner ∈ support,
        (exterior.filter fun vertex ↦ owner ∈ anchor vertex).card) =
      ∑ vertex ∈ exterior,
        (support.filter fun owner ↦ owner ∈ anchor vertex).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hfilter (vertex : α) (hvertex : vertex ∈ exterior) :
      support.filter (fun owner ↦ owner ∈ anchor vertex) = anchor vertex := by
    ext owner
    simp only [Finset.mem_filter]
    constructor
    · exact fun howner ↦ howner.2
    · exact fun howner ↦ ⟨hanchorSub vertex hvertex howner, howner⟩
  have htotal :
      (∑ owner ∈ support,
        (exterior.filter fun vertex ↦ owner ∈ anchor vertex).card) = 32 := by
    rw [hdoubleCount]
    calc
      (∑ vertex ∈ exterior,
          (support.filter fun owner ↦ owner ∈ anchor vertex).card) =
          ∑ vertex ∈ exterior, (anchor vertex).card := by
            apply Finset.sum_congr rfl
            intro vertex hvertex
            rw [hfilter vertex hvertex]
      _ = ∑ _vertex ∈ exterior, 4 := by
        apply Finset.sum_congr rfl
        exact hanchorCard
      _ = 32 := by simp [hexteriorCard]
  have hupper :
      (∑ owner ∈ support,
        (exterior.filter fun vertex ↦ owner ∈ anchor vertex).card) ≤ 28 := by
    calc
      (∑ owner ∈ support,
          (exterior.filter fun vertex ↦ owner ∈ anchor vertex).card) ≤
          ∑ _owner ∈ support, 4 := by
            apply Finset.sum_le_sum
            exact hdegreeLe
      _ = 28 := by simp [hsupportCard]
  omega

/-- Five four-point anchors through one vertex of a seven-point support force
two distinct anchors to share at least three support vertices. -/
theorem exists_distinct_anchorPair_three_inter_of_fiveFoldOwner
    {α : Type*} [DecidableEq α]
    (support exterior : Finset α) (anchor : α → Finset α)
    (hsupportCard : support.card = 7)
    (hanchorSub : ∀ vertex ∈ exterior, anchor vertex ⊆ support)
    (hanchorCard : ∀ vertex ∈ exterior, (anchor vertex).card = 4)
    {owner : α} (hownerSupport : owner ∈ support)
    (hownerDegree :
      5 ≤ (exterior.filter fun vertex ↦ owner ∈ anchor vertex).card) :
    ∃ q ∈ exterior, ∃ r ∈ exterior,
      q ≠ r ∧ 3 ≤ (anchor q ∩ anchor r).card := by
  classical
  let firstFiber := exterior.filter fun vertex ↦ owner ∈ anchor vertex
  let firstBase := support.erase owner
  let firstBlock : α → Finset α := fun vertex ↦ (anchor vertex).erase owner
  have hfirstFiberCard : 5 ≤ firstFiber.card := by
    simpa [firstFiber] using hownerDegree
  have hfirstBaseCard : firstBase.card = 6 := by
    simp only [firstBase]
    rw [Finset.card_erase_of_mem hownerSupport, hsupportCard]
  have hfirstBlockSub : ∀ vertex ∈ firstFiber,
      firstBlock vertex ⊆ firstBase := by
    intro vertex hvertex x hx
    have hvertexData := Finset.mem_filter.mp hvertex
    have hxData := Finset.mem_erase.mp hx
    exact Finset.mem_erase.mpr
      ⟨hxData.1, hanchorSub vertex hvertexData.1 hxData.2⟩
  have hfirstBlockCard : ∀ vertex ∈ firstFiber,
      (firstBlock vertex).card = 3 := by
    intro vertex hvertex
    have hvertexData := Finset.mem_filter.mp hvertex
    simp only [firstBlock]
    rw [Finset.card_erase_of_mem hvertexData.2,
      hanchorCard vertex hvertexData.1]
  have hfirstGt : 2 * firstBase.card < 3 * firstFiber.card := by
    omega
  obtain ⟨coowner, hcoownerBase, hcoownerDegree⟩ :=
    exists_owner_degree_gt_of_total_gt_capacity
      firstBase firstFiber firstBlock 3 2 hfirstBlockSub
        hfirstBlockCard hfirstGt
  let secondFiber := firstFiber.filter fun vertex ↦
    coowner ∈ firstBlock vertex
  let secondBase := firstBase.erase coowner
  let secondBlock : α → Finset α := fun vertex ↦
    (firstBlock vertex).erase coowner
  have hsecondFiberCard : 3 ≤ secondFiber.card := by
    simpa [secondFiber] using hcoownerDegree
  have hsecondBaseCard : secondBase.card = 5 := by
    simp only [secondBase]
    rw [Finset.card_erase_of_mem hcoownerBase, hfirstBaseCard]
  have hsecondBlockSub : ∀ vertex ∈ secondFiber,
      secondBlock vertex ⊆ secondBase := by
    intro vertex hvertex
    have hvertexFirst := (Finset.mem_filter.mp hvertex).1
    exact Finset.erase_subset_erase coowner
      (hfirstBlockSub vertex hvertexFirst)
  have hsecondBlockCard : ∀ vertex ∈ secondFiber,
      (secondBlock vertex).card = 2 := by
    intro vertex hvertex
    have hvertexData := Finset.mem_filter.mp hvertex
    simp only [secondBlock]
    rw [Finset.card_erase_of_mem hvertexData.2,
      hfirstBlockCard vertex hvertexData.1]
  have hsecondGt : 1 * secondBase.card < 2 * secondFiber.card := by
    omega
  obtain ⟨thirdowner, hthirdownerBase, hthirdownerDegree⟩ :=
    exists_owner_degree_gt_of_total_gt_capacity
      secondBase secondFiber secondBlock 2 1 hsecondBlockSub
        hsecondBlockCard hsecondGt
  let thirdFiber := secondFiber.filter fun vertex ↦
    thirdowner ∈ secondBlock vertex
  have hthirdFiberCard : 1 < thirdFiber.card := by
    simpa [thirdFiber] using hthirdownerDegree
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp hthirdFiberCard
  have hqSecond := (Finset.mem_filter.mp hq).1
  have hrSecond := (Finset.mem_filter.mp hr).1
  have hqFirst := (Finset.mem_filter.mp hqSecond).1
  have hrFirst := (Finset.mem_filter.mp hrSecond).1
  have hqExterior := (Finset.mem_filter.mp hqFirst).1
  have hrExterior := (Finset.mem_filter.mp hrFirst).1
  refine ⟨q, hqExterior, r, hrExterior, hqr, ?_⟩
  have hownerQ : owner ∈ anchor q := (Finset.mem_filter.mp hqFirst).2
  have hownerR : owner ∈ anchor r := (Finset.mem_filter.mp hrFirst).2
  have hcoownerQ : coowner ∈ anchor q :=
    (Finset.mem_erase.mp (Finset.mem_filter.mp hqSecond).2).2
  have hcoownerR : coowner ∈ anchor r :=
    (Finset.mem_erase.mp (Finset.mem_filter.mp hrSecond).2).2
  have hthirdownerQ : thirdowner ∈ anchor q :=
    (Finset.mem_erase.mp
      (Finset.mem_erase.mp (Finset.mem_filter.mp hq).2).2).2
  have hthirdownerR : thirdowner ∈ anchor r :=
    (Finset.mem_erase.mp
      (Finset.mem_erase.mp (Finset.mem_filter.mp hr).2).2).2
  have htripleSub : {owner, coowner, thirdowner} ⊆
      anchor q ∩ anchor r := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hownerQ, hownerR⟩
    · exact Finset.mem_inter.mpr ⟨hcoownerQ, hcoownerR⟩
    · exact Finset.mem_inter.mpr ⟨hthirdownerQ, hthirdownerR⟩
  have hcoownerNe : coowner ≠ owner :=
    (Finset.mem_erase.mp hcoownerBase).1
  have hthirdownerNeCo : thirdowner ≠ coowner :=
    (Finset.mem_erase.mp hthirdownerBase).1
  have hthirdownerNe : thirdowner ≠ owner :=
    (Finset.mem_erase.mp
      (Finset.mem_erase.mp hthirdownerBase).2).1
  calc
    3 = ({owner, coowner, thirdowner} : Finset α).card := by
      simp [hcoownerNe.symm, hthirdownerNeCo.symm,
        hthirdownerNe.symm]
    _ ≤ (anchor q ∩ anchor r).card := Finset.card_le_card htripleSub

/-- Two four-point blocks with a three-point overlap are either identical or
differ by exactly one point in each direction. -/
theorem four_blocks_three_inter_normalForm
    {α : Type*} [DecidableEq α] (a b : Finset α)
    (haCard : a.card = 4) (hbCard : b.card = 4)
    (hinter : 3 ≤ (a ∩ b).card) :
    a = b ∨
      (a ∩ b).card = 3 ∧ (a \ b).card = 1 ∧ (b \ a).card = 1 := by
  have hinterLe : (a ∩ b).card ≤ 4 := by
    calc
      (a ∩ b).card ≤ a.card := Finset.card_le_card Finset.inter_subset_left
      _ = 4 := haCard
  by_cases hinterFour : (a ∩ b).card = 4
  · apply Or.inl
    have hinterA : a ∩ b = a :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hinterB : a ∩ b = b :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hinterA.symm.trans hinterB
  · apply Or.inr
    have hinterThree : (a ∩ b).card = 3 := by omega
    have haDiff : (a \ b).card = 1 := by
      have hcard := Finset.card_inter_add_card_sdiff a b
      omega
    have hbDiff : (b \ a).card = 1 := by
      have hcard := Finset.card_inter_add_card_sdiff b a
      rw [Finset.inter_comm] at hcard
      omega
    exact ⟨hinterThree, haDiff, hbDiff⟩

/-- On fifteen points, failure of the predecessor-half conclusion has an
exact maximum-support form: seven support vertices, eight exterior vertices,
and a four-point strong-five anchor for every exterior vertex. -/
theorem predecessorHalfFin15_or_exactMaximumObstruction
    (χ : TripleColoring 15)
    (hone : OneChangeOn χ Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    (∃ support : Finset (Fin 15),
      ¬ContainsStrongPolygonSet χ support 5 ∧
        15 ≤ 2 * support.card) ∨
      ∃ support : Finset (Fin 15),
        IsMaximumPredecessorFreeSupport χ 6 support ∧
          support.card = 7 ∧
          (Finset.univ \ support).card = 8 ∧
          ∀ vertex ∈ Finset.univ \ support,
            ∃ anchor : Finset (Fin 15),
              anchor ⊆ support ∧ anchor.card = 4 ∧
                IsStrongPolygonSet χ (insert vertex anchor) := by
  let f : Fin 13 ↪o Fin 15 := Fin.castLEOrderEmb (by omega)
  have honeWindow :
      OneChangeOn χ (Finset.univ.image f) := by
    intro i j k l hij hjk hkl _hi _hj _hk _hl
    exact hone hij hjk hkl (by simp) (by simp) (by simp) (by simp)
  have hnoStrongWindow :
      ¬ContainsStrongPolygonSet χ (Finset.univ.image f) 6 := by
    intro hstrong
    exact hnoStrong
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
        (Finset.subset_univ _))
  obtain ⟨base, _hbaseSub, hbaseCard, hbaseFree⟩ :=
    predecessorFreeSevenSubsetAtSixFinThirteenWindow_of_oneChange
      χ f honeWindow hnoStrongWindow
  obtain ⟨support, hmaximum⟩ :=
    exists_maximumPredecessorFreeSupport (k := 6) χ (by omega)
  have hbaseLe : base.card ≤ support.card := hmaximum.2 base hbaseFree
  have hsevenLe : 7 ≤ support.card := by
    simpa [hbaseCard] using hbaseLe
  by_cases hhalf : 15 ≤ 2 * support.card
  · exact Or.inl ⟨support, hmaximum.1, hhalf⟩
  · have hsupportCard : support.card = 7 := by omega
    have houtsideCard : (Finset.univ \ support).card = 8 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ support)]
      simp [hsupportCard]
    refine Or.inr ⟨support, hmaximum, hsupportCard, houtsideCard, ?_⟩
    intro vertex hvertexOutside
    have hvertexNotSupport : vertex ∉ support :=
      (Finset.mem_sdiff.mp hvertexOutside).2
    obtain ⟨anchor, _hvertexAnchor, hanchorSub, hanchorCard,
        hanchorStrong⟩ := hmaximum.exists_exteriorAnchor hvertexNotSupport
    exact ⟨anchor, hanchorSub, by simpa using hanchorCard, hanchorStrong⟩

/-- The exact maximum-support obstruction can be sharpened to a five-fold
collision: one support vertex belongs to chosen strong-five anchors for at
least five distinct exterior vertices. -/
theorem predecessorHalfFin15_or_fiveFoldOwnerObstruction
    (χ : TripleColoring 15)
    (hone : OneChangeOn χ Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    (∃ support : Finset (Fin 15),
      ¬ContainsStrongPolygonSet χ support 5 ∧
        15 ≤ 2 * support.card) ∨
      ∃ support : Finset (Fin 15),
        ∃ anchor : Fin 15 → Finset (Fin 15),
          ∃ owner : Fin 15,
            IsMaximumPredecessorFreeSupport χ 6 support ∧
              support.card = 7 ∧
              (Finset.univ \ support).card = 8 ∧
              (∀ vertex ∈ Finset.univ \ support,
                anchor vertex ⊆ support ∧ (anchor vertex).card = 4 ∧
                  IsStrongPolygonSet χ (insert vertex (anchor vertex))) ∧
              owner ∈ support ∧
              5 ≤ ((Finset.univ \ support).filter fun vertex ↦
                owner ∈ anchor vertex).card := by
  rcases predecessorHalfFin15_or_exactMaximumObstruction χ hone hnoStrong with
    hhalf | ⟨support, hmaximum, hsupportCard, houtsideCard, hanchors⟩
  · exact Or.inl hhalf
  · classical
    let outside : Finset (Fin 15) := Finset.univ \ support
    let anchor : Fin 15 → Finset (Fin 15) := fun vertex ↦
      if hvertex : vertex ∈ outside then
        Classical.choose (hanchors vertex hvertex)
      else ∅
    have hanchorData : ∀ vertex ∈ outside,
        anchor vertex ⊆ support ∧ (anchor vertex).card = 4 ∧
          IsStrongPolygonSet χ (insert vertex (anchor vertex)) := by
      intro vertex hvertex
      simpa [anchor, hvertex] using
        Classical.choose_spec (hanchors vertex hvertex)
    obtain ⟨owner, howner, hownerDegree⟩ :=
      exists_fiveFoldOwner_of_seven_eight_fourAnchors
        support outside anchor hsupportCard houtsideCard
        (fun vertex hvertex ↦ (hanchorData vertex hvertex).1)
        (fun vertex hvertex ↦ (hanchorData vertex hvertex).2.1)
    exact Or.inr ⟨support, anchor, owner, hmaximum, hsupportCard,
      houtsideCard, hanchorData, howner, hownerDegree⟩

/-- The bad Fin15 branch contains two distinct exterior vertices whose
strong-five anchors overlap in at least three support vertices. -/
theorem predecessorHalfFin15_or_threeOverlapAnchorPairObstruction
    (χ : TripleColoring 15)
    (hone : OneChangeOn χ Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    (∃ support : Finset (Fin 15),
      ¬ContainsStrongPolygonSet χ support 5 ∧
        15 ≤ 2 * support.card) ∨
      ∃ support : Finset (Fin 15),
        ∃ anchor : Fin 15 → Finset (Fin 15),
          ∃ q ∈ Finset.univ \ support,
            ∃ r ∈ Finset.univ \ support,
              IsMaximumPredecessorFreeSupport χ 6 support ∧
                support.card = 7 ∧
                (Finset.univ \ support).card = 8 ∧
                (∀ vertex ∈ Finset.univ \ support,
                  anchor vertex ⊆ support ∧ (anchor vertex).card = 4 ∧
                    IsStrongPolygonSet χ (insert vertex (anchor vertex))) ∧
                q ≠ r ∧ 3 ≤ (anchor q ∩ anchor r).card := by
  rcases predecessorHalfFin15_or_fiveFoldOwnerObstruction
      χ hone hnoStrong with hhalf |
      ⟨support, anchor, owner, hmaximum, hsupportCard,
        houtsideCard, hanchorData, howner, hownerDegree⟩
  · exact Or.inl hhalf
  · obtain ⟨q, hq, r, hr, hqr, hinter⟩ :=
      exists_distinct_anchorPair_three_inter_of_fiveFoldOwner
        support (Finset.univ \ support) anchor hsupportCard
        (fun vertex hvertex ↦ (hanchorData vertex hvertex).1)
        (fun vertex hvertex ↦ (hanchorData vertex hvertex).2.1)
        howner hownerDegree
    exact Or.inr ⟨support, anchor, q, hq, r, hr, hmaximum,
      hsupportCard, houtsideCard, hanchorData, hqr, hinter⟩

/-- The three-overlap collision is independent of how one blocker is selected
for each exterior vertex: every complete selector has such a pair. -/
theorem predecessorHalfFin15_or_unavoidableThreeOverlapObstruction
    (χ : TripleColoring 15)
    (hone : OneChangeOn χ Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6) :
    (∃ support : Finset (Fin 15),
      ¬ContainsStrongPolygonSet χ support 5 ∧
        15 ≤ 2 * support.card) ∨
      ∃ support : Finset (Fin 15),
        IsMaximumPredecessorFreeSupport χ 6 support ∧
          support.card = 7 ∧
          (Finset.univ \ support).card = 8 ∧
          (∀ vertex ∈ Finset.univ \ support,
            ∃ blocker : Finset (Fin 15),
              blocker ⊆ support ∧ blocker.card = 4 ∧
                IsStrongPolygonSet χ (insert vertex blocker)) ∧
          ∀ anchor : Fin 15 → Finset (Fin 15),
            (∀ vertex ∈ Finset.univ \ support,
              anchor vertex ⊆ support ∧ (anchor vertex).card = 4 ∧
                IsStrongPolygonSet χ (insert vertex (anchor vertex))) →
              ∃ q ∈ Finset.univ \ support,
                ∃ r ∈ Finset.univ \ support,
                  q ≠ r ∧ 3 ≤ (anchor q ∩ anchor r).card ∧
                    (anchor q = anchor r ∨
                      (anchor q ∩ anchor r).card = 3 ∧
                        (anchor q \ anchor r).card = 1 ∧
                        (anchor r \ anchor q).card = 1) := by
  rcases predecessorHalfFin15_or_exactMaximumObstruction
      χ hone hnoStrong with hhalf |
      ⟨support, hmaximum, hsupportCard, houtsideCard, hblockers⟩
  · exact Or.inl hhalf
  · refine Or.inr ⟨support, hmaximum, hsupportCard, houtsideCard,
      hblockers, ?_⟩
    intro anchor hanchorData
    obtain ⟨owner, howner, hownerDegree⟩ :=
      exists_fiveFoldOwner_of_seven_eight_fourAnchors
        support (Finset.univ \ support) anchor hsupportCard houtsideCard
        (fun vertex hvertex ↦ (hanchorData vertex hvertex).1)
        (fun vertex hvertex ↦ (hanchorData vertex hvertex).2.1)
    obtain ⟨q, hq, r, hr, hqr, hinter⟩ :=
      exists_distinct_anchorPair_three_inter_of_fiveFoldOwner
        support (Finset.univ \ support) anchor hsupportCard
        (fun vertex hvertex ↦ (hanchorData vertex hvertex).1)
        (fun vertex hvertex ↦ (hanchorData vertex hvertex).2.1)
        howner hownerDegree
    exact ⟨q, hq, r, hr, hqr, hinter,
      four_blocks_three_inter_normalForm (anchor q) (anchor r)
        (hanchorData q hq).2.1 (hanchorData r hr).2.1 hinter⟩

end ErdosSzekeres

end
