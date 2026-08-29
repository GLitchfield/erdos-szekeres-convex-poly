module

public import ErdosSzekeres.PredecessorHalfFin15SharedAnchorCompatibility
public import ErdosSzekeres.PredecessorHalfFin15BlockerDesign
public import ErdosSzekeres.PredecessorHalfFin15SingleExchange

@[expose] public section

/-!
# The complete-system shared-anchor obstruction

The frozen raw contradiction requires more than the already known local
two-base defect.  The lemma below keeps that defect and simultaneously selects
a third member of the complete eight-vertex exterior system, together with all
of its anchor data.  The remaining obligation is a color compatibility bridge
between this third strong extension and one end of the defect quadruple.
-/

namespace ErdosSzekeres

/-- An eight-element exterior contains a vertex distinct from any prescribed
distinct pair in that exterior. -/
theorem exists_third_of_mem_of_mem_of_card_eight
    {outside : Finset (Fin 15)} {q r : Fin 15}
    (houtsideCard : outside.card = 8)
    (hq : q ∈ outside) (hr : r ∈ outside) (hqr : q ≠ r) :
    ∃ s ∈ outside, s ≠ q ∧ s ≠ r := by
  have hrErase : r ∈ outside.erase q :=
    Finset.mem_erase.mpr ⟨hqr.symm, hr⟩
  have heraseCard : ((outside.erase q).erase r).card = 6 := by
    rw [Finset.card_erase_of_mem hrErase, Finset.card_erase_of_mem hq,
      houtsideCard]
  have heraseNonempty : (outside.erase q).erase r |>.Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨s, hs⟩ := heraseNonempty
  have hsData := Finset.mem_erase.mp hs
  have hsOutsideData := Finset.mem_erase.mp hsData.2
  exact ⟨s, hsOutsideData.2, hsOutsideData.1, hsData.1⟩

/-- The genuinely atomic left branch: after explicitly excluding every
distinct three-overlap exchange, all eight indexed anchors retain the full
Fano/multiplicity alternative.  This theorem is global combinatorial data, not
the still-open raw contradiction. -/
theorem fin15ExteriorSystem_sharedAnchor_atomic_classification
    {support : Finset (Fin 15)}
    {anchor : Fin 15 → Finset (Fin 15)}
    (hsupportCard : support.card = 7)
    (houtsideCard : (Finset.univ \ support).card = 8)
    (hanchorSub : ∀ vertex ∈ Finset.univ \ support, anchor vertex ⊆ support)
    (hanchorCard : ∀ vertex ∈ Finset.univ \ support, (anchor vertex).card = 4)
    {q r : Fin 15}
    (_hq : q ∈ Finset.univ \ support)
    (_hr : r ∈ Finset.univ \ support)
    (_hqr : q ≠ r)
    (hshared : anchor q = anchor r)
    (hsmallInter : ∀ u ∈ Finset.univ \ support,
      ∀ v ∈ Finset.univ \ support, anchor u ≠ anchor v →
        (anchor u ∩ anchor v).card ≤ 2) :
    ∃ index : Fin 8 ≃ {vertex // vertex ∈ Finset.univ \ support},
      anchor q = anchor r ∧
      (let indexedAnchor : Fin 8 → Finset (Fin 15) := fun i ↦ anchor (index i).1
       let blocks := Finset.univ.image indexedAnchor
       (blocks.card = 7 ∧
          ∀ pair : Finset (Fin 15), pair ⊆ support → pair.card = 2 →
            ∃! block : Finset (Fin 15), block ∈ blocks ∧ pair ⊆ support \ block) ∨
        (blocks.card ≤ 6 ∧
          ((∃ block ∈ blocks,
              3 ≤ (Finset.univ.filter fun i : Fin 8 ↦ indexedAnchor i = block).card) ∨
            ∃ block₁ ∈ blocks, ∃ block₂ ∈ blocks, block₁ ≠ block₂ ∧
              2 ≤ (Finset.univ.filter fun i : Fin 8 ↦ indexedAnchor i = block₁).card ∧
              2 ≤ (Finset.univ.filter fun i : Fin 8 ↦ indexedAnchor i = block₂).card))) := by
  classical
  let outside : Finset (Fin 15) := Finset.univ \ support
  let index : Fin 8 ≃ {vertex // vertex ∈ outside} :=
    (outside.equivFinOfCardEq houtsideCard).symm
  let indexedAnchor : Fin 8 → Finset (Fin 15) := fun i ↦ anchor (index i).1
  let blocks : Finset (Finset (Fin 15)) := Finset.univ.image indexedAnchor
  have hindexedSub : ∀ i, indexedAnchor i ⊆ support := by
    intro i
    exact hanchorSub (index i).1 (by simpa [outside] using (index i).2)
  have hindexedCard : ∀ i, (indexedAnchor i).card = 4 := by
    intro i
    exact hanchorCard (index i).1 (by simpa [outside] using (index i).2)
  have hindexedSmall : ∀ i j, indexedAnchor i ≠ indexedAnchor j →
      (indexedAnchor i ∩ indexedAnchor j).card ≤ 2 := by
    intro i j hij
    exact hsmallInter (index i).1 (by simpa [outside] using (index i).2)
      (index j).1 (by simpa [outside] using (index j).2) hij
  have hclassification := eight_fourBlock_family_fano_classification
    support indexedAnchor hsupportCard hindexedSub hindexedCard hindexedSmall
  dsimp only at hclassification
  refine ⟨index, hshared, ?_⟩
  dsimp only
  by_cases hseven :
      (Finset.univ.image fun i : Fin 8 ↦ anchor (index i).1).card = 7
  · apply Or.inl
    refine ⟨hseven, ?_⟩
    simpa [indexedAnchor] using hclassification.2.1 (by
      simpa [indexedAnchor] using hseven)
  · have hblocksLe : blocks.card ≤ 7 := by
      simpa [blocks] using hclassification.1
    have hnotSeven : blocks.card ≠ 7 := by
      simpa [blocks, indexedAnchor] using hseven
    have hsix :
        (Finset.univ.image fun i : Fin 8 ↦ anchor (index i).1).card ≤ 6 := by
      change blocks.card ≤ 6
      omega
    apply Or.inr
    refine ⟨hsix, ?_⟩
    simpa [indexedAnchor] using hclassification.2.2 (by
      simpa [indexedAnchor] using hsix)

/-- Saturation of the seven-block complement-pair design: a new four-block
which has only small intersections with distinct design blocks was already a
design block. -/
theorem fano_fourBlock_saturation
    {α : Type*} [DecidableEq α]
    (support : Finset α) (blocks : Finset (Finset α)) (candidate : Finset α)
    (hsupportCard : support.card = 7)
    (hblockSub : ∀ block ∈ blocks, block ⊆ support)
    (hblockCard : ∀ block ∈ blocks, block.card = 4)
    (hfano : ∀ pair : Finset α, pair ⊆ support → pair.card = 2 →
      ∃! block : Finset α, block ∈ blocks ∧ pair ⊆ support \ block)
    (hcandidateSub : candidate ⊆ support)
    (hcandidateCard : candidate.card = 4)
    (hsmall : ∀ block ∈ blocks, candidate ≠ block →
      (candidate ∩ block).card ≤ 2) :
    candidate ∈ blocks := by
  have hcomplementCard : (support \ candidate).card = 3 := by
    rw [Finset.card_sdiff_of_subset hcandidateSub,
      hsupportCard, hcandidateCard]
  obtain ⟨pair, hpairSub, hpairCard⟩ :=
    Finset.exists_subset_card_eq (s := support \ candidate) (n := 2) (by
      omega)
  have hpairSupport : pair ⊆ support := hpairSub.trans Finset.sdiff_subset
  obtain ⟨block, ⟨hblock, hpairBlock⟩, _hunique⟩ :=
    hfano pair hpairSupport hpairCard
  have hpairCandidate : pair ∈ (support \ candidate).powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hpairSub, hpairCard⟩
  have hpairExisting : pair ∈ (support \ block).powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hpairBlock, hpairCard⟩
  have heq := fourBlock_eq_of_common_complement_pair
    support candidate block pair hsupportCard hcandidateSub
      (hblockSub block hblock) hcandidateCard (hblockCard block hblock)
      (fun hne ↦ hsmall block hblock hne) hpairCandidate hpairExisting
  exact heq.symm ▸ hblock

/-- Exact Fano saturation transition for a four-point candidate: it is an
existing block, or it has a distinct three-overlap with an existing block. -/
theorem fano_fourBlock_mem_or_threeOverlap
    {α : Type*} [DecidableEq α]
    (support : Finset α) (blocks : Finset (Finset α)) (candidate : Finset α)
    (hsupportCard : support.card = 7)
    (hblockSub : ∀ block ∈ blocks, block ⊆ support)
    (hblockCard : ∀ block ∈ blocks, block.card = 4)
    (hfano : ∀ pair : Finset α, pair ⊆ support → pair.card = 2 →
      ∃! block : Finset α, block ∈ blocks ∧ pair ⊆ support \ block)
    (hcandidateSub : candidate ⊆ support)
    (hcandidateCard : candidate.card = 4) :
    candidate ∈ blocks ∨
      ∃ block ∈ blocks, candidate ≠ block ∧
        3 ≤ (candidate ∩ block).card := by
  by_cases hcandidate : candidate ∈ blocks
  · exact Or.inl hcandidate
  · apply Or.inr
    by_contra hnone
    apply hcandidate
    apply fano_fourBlock_saturation support blocks candidate hsupportCard
      hblockSub hblockCard hfano hcandidateSub hcandidateCard
    intro block hblock hne
    by_contra hlarge
    apply hnone
    exact ⟨block, hblock, hne, by omega⟩

/-- Normal-form version of the neutral Fano selector transition: a new
four-block is already selected, or it makes an exact one-for-one exchange
with a selected block. -/
theorem fano_fourBlock_mem_or_singleExchange
    {α : Type*} [DecidableEq α]
    (support : Finset α) (blocks : Finset (Finset α)) (candidate : Finset α)
    (hsupportCard : support.card = 7)
    (hblockSub : ∀ block ∈ blocks, block ⊆ support)
    (hblockCard : ∀ block ∈ blocks, block.card = 4)
    (hfano : ∀ pair : Finset α, pair ⊆ support → pair.card = 2 →
      ∃! block : Finset α, block ∈ blocks ∧ pair ⊆ support \ block)
    (hcandidateSub : candidate ⊆ support)
    (hcandidateCard : candidate.card = 4) :
    candidate ∈ blocks ∨
      ∃ block ∈ blocks,
        (candidate ∩ block).card = 3 ∧
        (candidate \ block).card = 1 ∧
        (block \ candidate).card = 1 := by
  rcases fano_fourBlock_mem_or_threeOverlap support blocks candidate
      hsupportCard hblockSub hblockCard hfano hcandidateSub hcandidateCard with
    hmem | ⟨block, hblock, hne, hinter⟩
  · exact Or.inl hmem
  · apply Or.inr
    refine ⟨block, hblock, ?_⟩
    rcases four_blocks_three_inter_normalForm candidate block
        hcandidateCard (hblockCard block hblock) hinter with heq | hnormal
    · exact (hne heq).elim
    · exact hnormal

/-- Any three four-point blocks in a seven-point support have a two-point
transversal: one point hits the first two blocks and a distinct point hits the
third. -/
theorem exists_twoPoint_transversal_three_fourBlocks
    {α : Type*} [DecidableEq α]
    (support first second third : Finset α)
    (hsupportCard : support.card = 7)
    (hfirstSub : first ⊆ support) (hsecondSub : second ⊆ support)
    (_hthirdSub : third ⊆ support)
    (hfirstCard : first.card = 4) (hsecondCard : second.card = 4)
    (hthirdCard : third.card = 4) :
    ∃ x ∈ first ∩ second, ∃ y ∈ third, x ≠ y := by
  have hunionSub : first ∪ second ⊆ support :=
    Finset.union_subset hfirstSub hsecondSub
  have hunionLe : (first ∪ second).card ≤ 7 := by
    simpa [hsupportCard] using Finset.card_le_card hunionSub
  have hunionInter := Finset.card_union_add_card_inter first second
  have hinterPos : 0 < (first ∩ second).card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hinterPos
  have hthirdErasePos : 0 < (third.erase x).card := by
    by_cases hxThird : x ∈ third
    · rw [Finset.card_erase_of_mem hxThird, hthirdCard]
      omega
    · rw [Finset.erase_eq_of_notMem hxThird, hthirdCard]
      omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hthirdErasePos
  have hyData := Finset.mem_erase.mp hy
  exact ⟨x, hx, y, hyData.2, hyData.1.symm⟩

/-- The exact local residue carried by a non-strong union of two strong
one-vertex extensions of one four-point base. -/
def Fin15SharedPairDefect
    (chi : TripleColoring 15) (base : Finset (Fin 15)) (q r : Fin 15) : Prop :=
  ∃ i j k l : Fin 15, ∃ (hij : i < j) (hjk : j < k) (hkl : k < l),
    i ∈ insert q (insert r base) ∧
    j ∈ insert q (insert r base) ∧
    k ∈ insert q (insert r base) ∧
    l ∈ insert q (insert r base) ∧
    (q = i ∨ q = j ∨ q = k ∨ q = l) ∧
    (r = i ∨ r = j ∨ r = k ∨ r = l) ∧
    (({i, j, k, l} : Finset (Fin 15)) ∩ base).card = 2 ∧
    ((chi ⟨i, j, k, hij, hjk⟩ =
          chi ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
        chi ⟨i, k, l, hij.trans hjk, hkl⟩ ≠
          chi ⟨j, k, l, hjk, hkl⟩) ∨
      (chi ⟨i, j, k, hij, hjk⟩ ≠
          chi ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
        chi ⟨i, k, l, hij.trans hjk, hkl⟩ =
          chi ⟨j, k, l, hjk, hkl⟩))

/-- The forced strong-five witness trichotomy in a maximum-support exchange
candidate obtained by deleting `c` and adjoining `q,r`. -/
def Fin15ExchangeWitnessTrichotomy
    (chi : TripleColoring 15) (support : Finset (Fin 15))
    (q r c : Fin 15) : Prop :=
  (∃ residue : Finset (Fin 15),
    residue ⊆ support.erase c ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert q (insert r residue))) ∨
  (∃ base : Finset (Fin 15),
    base ⊆ support.erase c ∧ base.card = 4 ∧
      IsStrongPolygonSet chi (insert q base)) ∨
  ∃ base : Finset (Fin 15),
    base ⊆ support.erase c ∧ base.card = 4 ∧
      IsStrongPolygonSet chi (insert r base)

/-- Closed control: deleting a point outside `base` gives three formally
forced trichotomies for three exterior pairs.  This is premise-inert when
`base` is already a strong owner anchor, because `base ⊆ support.erase c`. -/
theorem fin15_threeExterior_omittedSupport_trichotomyGrid
    (chi : TripleColoring 15)
    {support base : Finset (Fin 15)} {q r s : Fin 15}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (hbaseSub : base ⊆ support)
    (hbaseCard : base.card = 4)
    (hq : q ∈ Finset.univ \ support)
    (hr : r ∈ Finset.univ \ support)
    (hs : s ∈ Finset.univ \ support)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    (support \ base).card = 3 ∧
      ∀ c ∈ support \ base,
        Fin15ExchangeWitnessTrichotomy chi support q r c ∧
        Fin15ExchangeWitnessTrichotomy chi support q s c ∧
        Fin15ExchangeWitnessTrichotomy chi support r s c := by
  have hcomplementCard : (support \ base).card = 3 := by
    rw [Finset.card_sdiff_of_subset hbaseSub, hsupportCard, hbaseCard]
  refine ⟨hcomplementCard, ?_⟩
  intro c hc
  have hcSupport : c ∈ support := (Finset.mem_sdiff.mp hc).1
  exact ⟨fin15_singleExchange_candidate_anchor_trichotomy
      chi hmaximum hsupportCard hq hr hqr hcSupport,
    fin15_singleExchange_candidate_anchor_trichotomy
      chi hmaximum hsupportCard hq hs hqs hcSupport,
    fin15_singleExchange_candidate_anchor_trichotomy
      chi hmaximum hsupportCard hr hs hrs hcSupport⟩

/-- Three exterior owners of one blocker yield simultaneous pair defects.  No
parity contradiction follows from the current API: maximal-support data using
the other three support vertices is the missing global input. -/
theorem fin15_threeSharedExtensions_pairDefects
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    {support base : Finset (Fin 15)} {q r s : Fin 15}
    (hbaseSub : base ⊆ support)
    (hbaseCard : base.card = 4)
    (hq : q ∈ Finset.univ \ support)
    (hr : r ∈ Finset.univ \ support)
    (hs : s ∈ Finset.univ \ support)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hqStrong : IsStrongPolygonSet chi (insert q base))
    (hrStrong : IsStrongPolygonSet chi (insert r base))
    (hsStrong : IsStrongPolygonSet chi (insert s base)) :
    Fin15SharedPairDefect chi base q r ∧
      Fin15SharedPairDefect chi base q s ∧
      Fin15SharedPairDefect chi base r s := by
  exact ⟨predecessorHalfFin15_sharedAnchor_singleEndDefect_twoBase
      chi hone hnoStrong hbaseSub hbaseCard hq hr hqr hqStrong hrStrong,
    predecessorHalfFin15_sharedAnchor_singleEndDefect_twoBase
      chi hone hnoStrong hbaseSub hbaseCard hq hs hqs hqStrong hsStrong,
    predecessorHalfFin15_sharedAnchor_singleEndDefect_twoBase
      chi hone hnoStrong hbaseSub hbaseCard hr hs hrs hrStrong hsStrong⟩

/-- A multiplicity-three fiber in the global classification reduces exactly
to three distinct exterior owners of one blocker and their three simultaneous
pair defects. -/
theorem fin15_threeFiber_pairDefects
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    {support : Finset (Fin 15)}
    {anchor : Fin 15 → Finset (Fin 15)}
    (hanchorData : ∀ vertex ∈ Finset.univ \ support,
      anchor vertex ⊆ support ∧
        (anchor vertex).card = 4 ∧
        IsStrongPolygonSet chi (insert vertex (anchor vertex)))
    (index : Fin 8 ≃ {vertex // vertex ∈ Finset.univ \ support})
    (block : Finset (Fin 15))
    (hthree : 3 ≤ (Finset.univ.filter fun i : Fin 8 ↦ anchor (index i).1 = block).card) :
    ∃ q ∈ Finset.univ \ support,
      ∃ r ∈ Finset.univ \ support,
        ∃ s ∈ Finset.univ \ support,
          q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
          anchor q = block ∧ anchor r = block ∧ anchor s = block ∧
          Fin15SharedPairDefect chi block q r ∧
          Fin15SharedPairDefect chi block q s ∧
          Fin15SharedPairDefect chi block r s := by
  classical
  let fiber : Finset (Fin 8) :=
    Finset.univ.filter fun i : Fin 8 ↦ anchor (index i).1 = block
  obtain ⟨triple, htripleSub, htripleCard⟩ :=
    Finset.exists_subset_card_eq (s := fiber) (n := 3) (by simpa [fiber] using hthree)
  obtain ⟨i, j, k, hij, hik, hjk, htripleEq⟩ := Finset.card_eq_three.mp htripleCard
  have hiFiber : i ∈ fiber := htripleSub (by simp [htripleEq])
  have hjFiber : j ∈ fiber := htripleSub (by simp [htripleEq])
  have hkFiber : k ∈ fiber := htripleSub (by simp [htripleEq])
  have hiBlock : anchor (index i).1 = block := (Finset.mem_filter.mp hiFiber).2
  have hjBlock : anchor (index j).1 = block := (Finset.mem_filter.mp hjFiber).2
  have hkBlock : anchor (index k).1 = block := (Finset.mem_filter.mp hkFiber).2
  have hqi : (index i).1 ∈ Finset.univ \ support := (index i).2
  have hrj : (index j).1 ∈ Finset.univ \ support := (index j).2
  have hsk : (index k).1 ∈ Finset.univ \ support := (index k).2
  have hqneR : (index i).1 ≠ (index j).1 := by
    intro hvertices
    exact hij (index.injective (Subtype.ext hvertices))
  have hqneS : (index i).1 ≠ (index k).1 := by
    intro hvertices
    exact hik (index.injective (Subtype.ext hvertices))
  have hrneS : (index j).1 ≠ (index k).1 := by
    intro hvertices
    exact hjk (index.injective (Subtype.ext hvertices))
  have hiData := hanchorData (index i).1 hqi
  have hjData := hanchorData (index j).1 hrj
  have hkData := hanchorData (index k).1 hsk
  have hblockSub : block ⊆ support := by simpa [hiBlock] using hiData.1
  have hblockCard : block.card = 4 := by simpa [hiBlock] using hiData.2.1
  have hiStrong : IsStrongPolygonSet chi (insert (index i).1 block) := by
    simpa [hiBlock] using hiData.2.2
  have hjStrong : IsStrongPolygonSet chi (insert (index j).1 block) := by
    simpa [hjBlock] using hjData.2.2
  have hkStrong : IsStrongPolygonSet chi (insert (index k).1 block) := by
    simpa [hkBlock] using hkData.2.2
  have hdefects := fin15_threeSharedExtensions_pairDefects
    chi hone hnoStrong hblockSub hblockCard hqi hrj hsk hqneR hqneS hrneS
      hiStrong hjStrong hkStrong
  exact ⟨(index i).1, hqi, (index j).1, hrj, (index k).1, hsk,
    hqneR, hqneS, hrneS, hiBlock, hjBlock, hkBlock,
    hdefects.1, hdefects.2.1, hdefects.2.2⟩

/-- Closed control combining the three pair defects with the premise-inert
trichotomy grid over support points omitted by the shared block. -/
theorem fin15_threeFiber_pairDefects_and_trichotomyGrid
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    {support : Finset (Fin 15)}
    {anchor : Fin 15 → Finset (Fin 15)}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (hanchorData : ∀ vertex ∈ Finset.univ \ support,
      anchor vertex ⊆ support ∧
        (anchor vertex).card = 4 ∧
        IsStrongPolygonSet chi (insert vertex (anchor vertex)))
    (index : Fin 8 ≃ {vertex // vertex ∈ Finset.univ \ support})
    (block : Finset (Fin 15))
    (hthree : 3 ≤ (Finset.univ.filter fun i : Fin 8 ↦ anchor (index i).1 = block).card) :
    ∃ q ∈ Finset.univ \ support,
      ∃ r ∈ Finset.univ \ support,
        ∃ s ∈ Finset.univ \ support,
          q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
          anchor q = block ∧ anchor r = block ∧ anchor s = block ∧
          Fin15SharedPairDefect chi block q r ∧
          Fin15SharedPairDefect chi block q s ∧
          Fin15SharedPairDefect chi block r s ∧
          (support \ block).card = 3 ∧
          ∀ c ∈ support \ block,
            Fin15ExchangeWitnessTrichotomy chi support q r c ∧
            Fin15ExchangeWitnessTrichotomy chi support q s c ∧
            Fin15ExchangeWitnessTrichotomy chi support r s c := by
  obtain ⟨q, hq, r, hr, s, hs, hqr, hqs, hrs,
      hqBlock, hrBlock, hsBlock, hqrDefect, hqsDefect, hrsDefect⟩ :=
    fin15_threeFiber_pairDefects chi hone hnoStrong hanchorData index block hthree
  have hqData := hanchorData q hq
  have hblockSub : block ⊆ support := by simpa [hqBlock] using hqData.1
  have hblockCard : block.card = 4 := by simpa [hqBlock] using hqData.2.1
  have hgrid := fin15_threeExterior_omittedSupport_trichotomyGrid
    chi hmaximum hsupportCard hblockSub hblockCard hq hr hs hqr hqs hrs
  exact ⟨q, hq, r, hr, s, hs, hqr, hqs, hrs,
    hqBlock, hrBlock, hsBlock, hqrDefect, hqsDefect, hrsDefect,
    hgrid.1, hgrid.2⟩

/-- The seven nonempty membership patterns of a witness among three specified
exterior vertices. -/
def Fin15ThreeExteriorWitnessPattern
    (polygon : Finset (Fin 15)) (q r s : Fin 15) : Prop :=
  (q ∈ polygon ∧ r ∈ polygon ∧ s ∈ polygon) ∨
  (q ∈ polygon ∧ r ∈ polygon ∧ s ∉ polygon) ∨
  (q ∈ polygon ∧ r ∉ polygon ∧ s ∈ polygon) ∨
  (q ∉ polygon ∧ r ∈ polygon ∧ s ∈ polygon) ∨
  (q ∈ polygon ∧ r ∉ polygon ∧ s ∉ polygon) ∨
  (q ∉ polygon ∧ r ∈ polygon ∧ s ∉ polygon) ∨
  (q ∉ polygon ∧ r ∉ polygon ∧ s ∈ polygon)

/-- The exact seven-way strong-five classification after adjoining three
exterior vertices to a twice-erased support. -/
def Fin15ThreeExteriorDoubleEraseWitness
    (chi : TripleColoring 15) (support : Finset (Fin 15))
    (q r s c d : Fin 15) : Prop :=
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase c).erase d ∧ residue.card = 2 ∧
      IsStrongPolygonSet chi (insert q (insert r (insert s residue)))) ∨
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase c).erase d ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert q (insert r residue))) ∨
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase c).erase d ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert q (insert s residue))) ∨
  (∃ residue : Finset (Fin 15),
    residue ⊆ (support.erase c).erase d ∧ residue.card = 3 ∧
      IsStrongPolygonSet chi (insert r (insert s residue))) ∨
  (∃ anchor : Finset (Fin 15),
    anchor ⊆ (support.erase c).erase d ∧ anchor.card = 4 ∧
      IsStrongPolygonSet chi (insert q anchor)) ∨
  (∃ anchor : Finset (Fin 15),
    anchor ⊆ (support.erase c).erase d ∧ anchor.card = 4 ∧
      IsStrongPolygonSet chi (insert r anchor)) ∨
  ∃ anchor : Finset (Fin 15),
    anchor ⊆ (support.erase c).erase d ∧ anchor.card = 4 ∧
      IsStrongPolygonSet chi (insert s anchor)

/-- Deleting two distinct support vertices and adjoining three distinct
exterior vertices preserves cardinality eight. -/
theorem fin15_threeExterior_doubleErase_candidate_card
    {support : Finset (Fin 15)} {q r s c d : Fin 15}
    (hsupportCard : support.card = 7)
    (hq : q ∈ Finset.univ \ support)
    (hr : r ∈ Finset.univ \ support)
    (hs : s ∈ Finset.univ \ support)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hc : c ∈ support) (hd : d ∈ support) (hcd : c ≠ d) :
    (insert q (insert r (insert s ((support.erase c).erase d)))).card = 8 := by
  have hdErase : d ∈ support.erase c := Finset.mem_erase.mpr ⟨hcd.symm, hd⟩
  have hdoubleCard : ((support.erase c).erase d).card = 5 := by
    rw [Finset.card_erase_of_mem hdErase, Finset.card_erase_of_mem hc,
      hsupportCard]
  have hqNotSupport : q ∉ support := (Finset.mem_sdiff.mp hq).2
  have hrNotSupport : r ∉ support := (Finset.mem_sdiff.mp hr).2
  have hsNotSupport : s ∉ support := (Finset.mem_sdiff.mp hs).2
  have hqNotDouble : q ∉ (support.erase c).erase d := fun hmem ↦
    hqNotSupport (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).2
  have hrNotDouble : r ∉ (support.erase c).erase d := fun hmem ↦
    hrNotSupport (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).2
  have hsNotDouble : s ∉ (support.erase c).erase d := fun hmem ↦
    hsNotSupport (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).2
  have hrNotInsert : r ∉ insert s ((support.erase c).erase d) := by
    simp [hrs, hrNotDouble]
  have hqNotInsert : q ∉ insert r (insert s ((support.erase c).erase d)) := by
    simp [hqr, hqs, hqNotDouble]
  rw [Finset.card_insert_of_notMem hqNotInsert,
    Finset.card_insert_of_notMem hrNotInsert,
    Finset.card_insert_of_notMem hsNotDouble, hdoubleCard]

/-- An exact seven-way residue decomposition of any strong five contained in
a three-exterior extension of a base set. -/
theorem fin15_threeExterior_exactWitness_of_polygon
    (chi : TripleColoring 15)
    {support : Finset (Fin 15)} {q r s c d : Fin 15}
    {polygon : Finset (Fin 15)}
    (hpolygonSub :
      polygon ⊆ insert q (insert r (insert s ((support.erase c).erase d))))
    (hpolygonCard : polygon.card = 5)
    (hpolygonStrong : IsStrongPolygonSet chi polygon)
    (hexterior : q ∈ polygon ∨ r ∈ polygon ∨ s ∈ polygon)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    Fin15ThreeExteriorDoubleEraseWitness chi support q r s c d := by
  have hbaseOfMem (x : Fin 15) (hx : x ∈ polygon)
      (hxq : x ≠ q) (hxr : x ≠ r) (hxs : x ≠ s) :
      x ∈ (support.erase c).erase d := by
    have hxCandidate := hpolygonSub hx
    simp only [Finset.mem_insert] at hxCandidate
    rcases hxCandidate with rfl | rfl | rfl | hxBase
    · exact (hxq rfl).elim
    · exact (hxr rfl).elim
    · exact (hxs rfl).elim
    · exact hxBase
  by_cases hqPolygon : q ∈ polygon
  · by_cases hrPolygon : r ∈ polygon
    · by_cases hsPolygon : s ∈ polygon
      · apply Or.inl
        let residue := ((polygon.erase q).erase r).erase s
        have hrEraseQ : r ∈ polygon.erase q :=
          Finset.mem_erase.mpr ⟨hqr.symm, hrPolygon⟩
        have hsEraseR : s ∈ (polygon.erase q).erase r :=
          Finset.mem_erase.mpr ⟨hrs.symm,
            Finset.mem_erase.mpr ⟨hqs.symm, hsPolygon⟩⟩
        have hresidueSub : residue ⊆ (support.erase c).erase d := by
          intro x hx
          have hxS := Finset.mem_erase.mp hx
          have hxR := Finset.mem_erase.mp hxS.2
          have hxQ := Finset.mem_erase.mp hxR.2
          exact hbaseOfMem x hxQ.2 hxQ.1 hxR.1 hxS.1
        have hresidueCard : residue.card = 2 := by
          simp only [residue]
          rw [Finset.card_erase_of_mem hsEraseR,
            Finset.card_erase_of_mem hrEraseQ,
            Finset.card_erase_of_mem hqPolygon, hpolygonCard]
        have hinsert : insert q (insert r (insert s residue)) = polygon := by
          simp only [residue]
          rw [Finset.insert_erase hsEraseR,
            Finset.insert_erase hrEraseQ, Finset.insert_erase hqPolygon]
        exact ⟨residue, hresidueSub, hresidueCard,
          hinsert.symm ▸ hpolygonStrong⟩
      · apply Or.inr
        apply Or.inl
        let residue := (polygon.erase q).erase r
        have hrEraseQ : r ∈ polygon.erase q :=
          Finset.mem_erase.mpr ⟨hqr.symm, hrPolygon⟩
        have hresidueSub : residue ⊆ (support.erase c).erase d := by
          intro x hx
          have hxR := Finset.mem_erase.mp hx
          have hxQ := Finset.mem_erase.mp hxR.2
          have hxs : x ≠ s := by
            intro hxs
            subst x
            exact hsPolygon hxQ.2
          exact hbaseOfMem x hxQ.2 hxQ.1 hxR.1 hxs
        have hresidueCard : residue.card = 3 := by
          simp only [residue]
          rw [Finset.card_erase_of_mem hrEraseQ,
            Finset.card_erase_of_mem hqPolygon, hpolygonCard]
        have hinsert : insert q (insert r residue) = polygon := by
          simp only [residue]
          rw [Finset.insert_erase hrEraseQ, Finset.insert_erase hqPolygon]
        exact ⟨residue, hresidueSub, hresidueCard,
          hinsert.symm ▸ hpolygonStrong⟩
    · by_cases hsPolygon : s ∈ polygon
      · apply Or.inr
        apply Or.inr
        apply Or.inl
        let residue := (polygon.erase q).erase s
        have hsEraseQ : s ∈ polygon.erase q :=
          Finset.mem_erase.mpr ⟨hqs.symm, hsPolygon⟩
        have hresidueSub : residue ⊆ (support.erase c).erase d := by
          intro x hx
          have hxS := Finset.mem_erase.mp hx
          have hxQ := Finset.mem_erase.mp hxS.2
          have hxr : x ≠ r := by
            intro hxr
            subst x
            exact hrPolygon hxQ.2
          exact hbaseOfMem x hxQ.2 hxQ.1 hxr hxS.1
        have hresidueCard : residue.card = 3 := by
          simp only [residue]
          rw [Finset.card_erase_of_mem hsEraseQ,
            Finset.card_erase_of_mem hqPolygon, hpolygonCard]
        have hinsert : insert q (insert s residue) = polygon := by
          simp only [residue]
          rw [Finset.insert_erase hsEraseQ, Finset.insert_erase hqPolygon]
        exact ⟨residue, hresidueSub, hresidueCard,
          hinsert.symm ▸ hpolygonStrong⟩
      · apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        let anchor := polygon.erase q
        have hanchorSub : anchor ⊆ (support.erase c).erase d := by
          intro x hx
          have hxQ := Finset.mem_erase.mp hx
          have hxr : x ≠ r := by
            intro hxr
            subst x
            exact hrPolygon hxQ.2
          have hxs : x ≠ s := by
            intro hxs
            subst x
            exact hsPolygon hxQ.2
          exact hbaseOfMem x hxQ.2 hxQ.1 hxr hxs
        have hanchorCard : anchor.card = 4 := by
          simp only [anchor]
          rw [Finset.card_erase_of_mem hqPolygon, hpolygonCard]
        have hinsert : insert q anchor = polygon := Finset.insert_erase hqPolygon
        exact ⟨anchor, hanchorSub, hanchorCard,
          hinsert.symm ▸ hpolygonStrong⟩
  · by_cases hrPolygon : r ∈ polygon
    · by_cases hsPolygon : s ∈ polygon
      · apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        let residue := (polygon.erase r).erase s
        have hsEraseR : s ∈ polygon.erase r :=
          Finset.mem_erase.mpr ⟨hrs.symm, hsPolygon⟩
        have hresidueSub : residue ⊆ (support.erase c).erase d := by
          intro x hx
          have hxS := Finset.mem_erase.mp hx
          have hxR := Finset.mem_erase.mp hxS.2
          have hxq : x ≠ q := by
            intro hxq
            subst x
            exact hqPolygon hxR.2
          exact hbaseOfMem x hxR.2 hxq hxR.1 hxS.1
        have hresidueCard : residue.card = 3 := by
          simp only [residue]
          rw [Finset.card_erase_of_mem hsEraseR,
            Finset.card_erase_of_mem hrPolygon, hpolygonCard]
        have hinsert : insert r (insert s residue) = polygon := by
          simp only [residue]
          rw [Finset.insert_erase hsEraseR, Finset.insert_erase hrPolygon]
        exact ⟨residue, hresidueSub, hresidueCard,
          hinsert.symm ▸ hpolygonStrong⟩
      · apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        let anchor := polygon.erase r
        have hanchorSub : anchor ⊆ (support.erase c).erase d := by
          intro x hx
          have hxR := Finset.mem_erase.mp hx
          have hxq : x ≠ q := by
            intro hxq
            subst x
            exact hqPolygon hxR.2
          have hxs : x ≠ s := by
            intro hxs
            subst x
            exact hsPolygon hxR.2
          exact hbaseOfMem x hxR.2 hxq hxR.1 hxs
        have hanchorCard : anchor.card = 4 := by
          simp only [anchor]
          rw [Finset.card_erase_of_mem hrPolygon, hpolygonCard]
        have hinsert : insert r anchor = polygon := Finset.insert_erase hrPolygon
        exact ⟨anchor, hanchorSub, hanchorCard,
          hinsert.symm ▸ hpolygonStrong⟩
    · have hsPolygon : s ∈ polygon :=
        (hexterior.resolve_left hqPolygon).resolve_left hrPolygon
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      let anchor := polygon.erase s
      have hanchorSub : anchor ⊆ (support.erase c).erase d := by
        intro x hx
        have hxS := Finset.mem_erase.mp hx
        have hxq : x ≠ q := by
          intro hxq
          subst x
          exact hqPolygon hxS.2
        have hxr : x ≠ r := by
          intro hxr
          subst x
          exact hrPolygon hxS.2
        exact hbaseOfMem x hxS.2 hxq hxr hxS.1
      have hanchorCard : anchor.card = 4 := by
        simp only [anchor]
        rw [Finset.card_erase_of_mem hsPolygon, hpolygonCard]
      have hinsert : insert s anchor = polygon := Finset.insert_erase hsPolygon
      exact ⟨anchor, hanchorSub, hanchorCard,
        hinsert.symm ▸ hpolygonStrong⟩

/-- The first non-premise-inert maximum-support coupling for a shared
three-owner block: erase two distinct block vertices, force a strong five in
the resulting eight-set, classify its one/two/three exterior-owner pattern,
and certify that at most two vertices of the original block survive. -/
theorem fin15_threeExterior_doubleBaseErase_forcedWitness
    (chi : TripleColoring 15)
    {support base : Finset (Fin 15)} {q r s c d : Fin 15}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (hbaseSub : base ⊆ support)
    (hbaseCard : base.card = 4)
    (hq : q ∈ Finset.univ \ support)
    (hr : r ∈ Finset.univ \ support)
    (hs : s ∈ Finset.univ \ support)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hc : c ∈ base) (hd : d ∈ base) (hcd : c ≠ d) :
    ∃ polygon : Finset (Fin 15),
      polygon ⊆ insert q (insert r (insert s ((support.erase c).erase d))) ∧
      polygon.card = 5 ∧
      IsStrongPolygonSet chi polygon ∧
      Fin15ThreeExteriorWitnessPattern polygon q r s ∧
      (polygon ∩ base).card ≤ 2 := by
  let candidate := insert q (insert r (insert s ((support.erase c).erase d)))
  have hcSupport : c ∈ support := hbaseSub hc
  have hdSupport : d ∈ support := hbaseSub hd
  have hcandidateCard : candidate.card = 8 := by
    exact fin15_threeExterior_doubleErase_candidate_card hsupportCard
      hq hr hs hqr hqs hrs hcSupport hdSupport hcd
  have hcontains : ContainsStrongPolygonSet chi candidate 5 := by
    by_contra hfree
    have hle := hmaximum.2 candidate hfree
    omega
  obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hcontains
  have hpattern : Fin15ThreeExteriorWitnessPattern polygon q r s := by
    by_cases hqPolygon : q ∈ polygon
    · by_cases hrPolygon : r ∈ polygon
      · by_cases hsPolygon : s ∈ polygon <;>
          simp [Fin15ThreeExteriorWitnessPattern, hqPolygon, hrPolygon, hsPolygon]
      · by_cases hsPolygon : s ∈ polygon <;>
          simp [Fin15ThreeExteriorWitnessPattern, hqPolygon, hrPolygon, hsPolygon]
    · by_cases hrPolygon : r ∈ polygon
      · by_cases hsPolygon : s ∈ polygon <;>
          simp [Fin15ThreeExteriorWitnessPattern, hqPolygon, hrPolygon, hsPolygon]
      · by_cases hsPolygon : s ∈ polygon
        · simp [Fin15ThreeExteriorWitnessPattern, hqPolygon, hrPolygon, hsPolygon]
        · exfalso
          apply hmaximum.1
          refine ⟨polygon, ?_, hpolygonCard, hpolygonStrong⟩
          intro x hx
          have hxCandidate := hpolygonSub hx
          simp only [candidate, Finset.mem_insert] at hxCandidate
          rcases hxCandidate with rfl | rfl | rfl | hxSupport
          · exact (hqPolygon hx).elim
          · exact (hrPolygon hx).elim
          · exact (hsPolygon hx).elim
          · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hxSupport).2).2
  have hdBaseErase : d ∈ base.erase c := Finset.mem_erase.mpr ⟨hcd.symm, hd⟩
  have hbaseDoubleCard : ((base.erase c).erase d).card = 2 := by
    rw [Finset.card_erase_of_mem hdBaseErase,
      Finset.card_erase_of_mem hc, hbaseCard]
  have hinterSub : polygon ∩ base ⊆ (base.erase c).erase d := by
    intro x hx
    have hxData := Finset.mem_inter.mp hx
    have hxCandidate := hpolygonSub hxData.1
    simp only [candidate, Finset.mem_insert] at hxCandidate
    rcases hxCandidate with rfl | rfl | rfl | hxDouble
    · exact ((Finset.mem_sdiff.mp hq).2 (hbaseSub hxData.2)).elim
    · exact ((Finset.mem_sdiff.mp hr).2 (hbaseSub hxData.2)).elim
    · exact ((Finset.mem_sdiff.mp hs).2 (hbaseSub hxData.2)).elim
    · have hxDoubleData := Finset.mem_erase.mp hxDouble
      have hxEraseData := Finset.mem_erase.mp hxDoubleData.2
      exact Finset.mem_erase.mpr
        ⟨hxDoubleData.1, Finset.mem_erase.mpr ⟨hxEraseData.1, hxData.2⟩⟩
  have hinterCard : (polygon ∩ base).card ≤ 2 := by
    calc
      (polygon ∩ base).card ≤ ((base.erase c).erase d).card :=
        Finset.card_le_card hinterSub
      _ = 2 := hbaseDoubleCard
  exact ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong, hpattern, hinterCard⟩

/-- Exact residue-form strengthening of
`fin15_threeExterior_doubleBaseErase_forcedWitness`. -/
theorem fin15_threeExterior_doubleBaseErase_forcedWitness_exact
    (chi : TripleColoring 15)
    {support base : Finset (Fin 15)} {q r s c d : Fin 15}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (hbaseSub : base ⊆ support)
    (hbaseCard : base.card = 4)
    (hq : q ∈ Finset.univ \ support)
    (hr : r ∈ Finset.univ \ support)
    (hs : s ∈ Finset.univ \ support)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hc : c ∈ base) (hd : d ∈ base) (hcd : c ≠ d) :
    ∃ polygon : Finset (Fin 15),
      polygon ⊆ insert q (insert r (insert s ((support.erase c).erase d))) ∧
      polygon.card = 5 ∧
      IsStrongPolygonSet chi polygon ∧
      Fin15ThreeExteriorWitnessPattern polygon q r s ∧
      Fin15ThreeExteriorDoubleEraseWitness chi support q r s c d ∧
      (polygon ∩ base).card ≤ 2 := by
  obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong,
      hpattern, hinterCard⟩ :=
    fin15_threeExterior_doubleBaseErase_forcedWitness
      chi hmaximum hsupportCard hbaseSub hbaseCard
        hq hr hs hqr hqs hrs hc hd hcd
  have hexterior : q ∈ polygon ∨ r ∈ polygon ∨ s ∈ polygon := by
    rcases hpattern with hqrs | hqrs | hqrs | hqrs | hqrs | hqrs | hqrs
    · exact Or.inl hqrs.1
    · exact Or.inl hqrs.1
    · exact Or.inl hqrs.1
    · exact Or.inr (Or.inl hqrs.2.1)
    · exact Or.inl hqrs.1
    · exact Or.inr (Or.inl hqrs.2.1)
    · exact Or.inr (Or.inr hqrs.2.2)
  have hexact := fin15_threeExterior_exactWitness_of_polygon
    chi hpolygonSub hpolygonCard hpolygonStrong hexterior hqr hqs hrs
  exact ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong,
    hpattern, hexact, hinterCard⟩

/-- Uniform three-anchor transversal coupling.  The chosen two-point deletion
kills all three supplied four-blocks, and maximality forces an exactly
classified strong-five witness in the resulting eight-set. -/
theorem fin15_threeAnchors_transversal_forcedWitness
    (chi : TripleColoring 15)
    {support first second third : Finset (Fin 15)} {q r s : Fin 15}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (hfirstSub : first ⊆ support) (hsecondSub : second ⊆ support)
    (hthirdSub : third ⊆ support)
    (hfirstCard : first.card = 4) (hsecondCard : second.card = 4)
    (hthirdCard : third.card = 4)
    (hq : q ∈ Finset.univ \ support)
    (hr : r ∈ Finset.univ \ support)
    (hs : s ∈ Finset.univ \ support)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    ∃ x ∈ first ∩ second, ∃ y ∈ third, x ≠ y ∧
      ¬first ⊆ (support.erase x).erase y ∧
      ¬second ⊆ (support.erase x).erase y ∧
      ¬third ⊆ (support.erase x).erase y ∧
      ∃ polygon : Finset (Fin 15),
        polygon ⊆ insert q (insert r (insert s ((support.erase x).erase y))) ∧
        polygon.card = 5 ∧
        IsStrongPolygonSet chi polygon ∧
        Fin15ThreeExteriorDoubleEraseWitness chi support q r s x y := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_twoPoint_transversal_three_fourBlocks
    support first second third hsupportCard hfirstSub hsecondSub hthirdSub
      hfirstCard hsecondCard hthirdCard
  have hxSupport : x ∈ support := hfirstSub (Finset.mem_inter.mp hx).1
  have hySupport : y ∈ support := hthirdSub hy
  have hxNotDouble : x ∉ (support.erase x).erase y := by simp
  have hyNotDouble : y ∉ (support.erase x).erase y := by simp
  have hfirstKilled : ¬first ⊆ (support.erase x).erase y := by
    intro hsub
    exact hxNotDouble (hsub (Finset.mem_inter.mp hx).1)
  have hsecondKilled : ¬second ⊆ (support.erase x).erase y := by
    intro hsub
    exact hxNotDouble (hsub (Finset.mem_inter.mp hx).2)
  have hthirdKilled : ¬third ⊆ (support.erase x).erase y := by
    intro hsub
    exact hyNotDouble (hsub hy)
  let candidate := insert q (insert r (insert s ((support.erase x).erase y)))
  have hcandidateCard : candidate.card = 8 := by
    exact fin15_threeExterior_doubleErase_candidate_card hsupportCard
      hq hr hs hqr hqs hrs hxSupport hySupport hxy
  have hcontains : ContainsStrongPolygonSet chi candidate 5 := by
    by_contra hfree
    have hle := hmaximum.2 candidate hfree
    omega
  obtain ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩ := hcontains
  have hexterior : q ∈ polygon ∨ r ∈ polygon ∨ s ∈ polygon := by
    by_contra hnone
    push Not at hnone
    apply hmaximum.1
    refine ⟨polygon, ?_, hpolygonCard, hpolygonStrong⟩
    intro z hz
    have hzCandidate := hpolygonSub hz
    simp only [candidate, Finset.mem_insert] at hzCandidate
    rcases hzCandidate with rfl | rfl | rfl | hzSupport
    · exact (hnone.1 hz).elim
    · exact (hnone.2.1 hz).elim
    · exact (hnone.2.2 hz).elim
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzSupport).2).2
  have hexact := fin15_threeExterior_exactWitness_of_polygon
    chi hpolygonSub hpolygonCard hpolygonStrong hexterior hqr hqs hrs
  exact ⟨x, hx, y, hy, hxy, hfirstKilled, hsecondKilled, hthirdKilled,
    polygon, hpolygonSub, hpolygonCard, hpolygonStrong, hexact⟩

/-- The discriminating Fano consumer for a transversal-forced witness.  A
multi-owner strong five remains as an explicit residue; a one-owner witness
is a genuinely alternative anchor and saturates to either an existing block
or an exact single exchange.  No well-founded decrease is asserted. -/
theorem fano_transversalWitness_multiOwner_or_reselector
    (chi : TripleColoring 15)
    {support : Finset (Fin 15)}
    (blocks : Finset (Finset (Fin 15)))
    (first second third : Finset (Fin 15))
    (q r s x y : Fin 15)
    (hsupportCard : support.card = 7)
    (hblockSub : ∀ block ∈ blocks, block ⊆ support)
    (hblockCard : ∀ block ∈ blocks, block.card = 4)
    (hfano : ∀ pair : Finset (Fin 15), pair ⊆ support → pair.card = 2 →
      ∃! block : Finset (Fin 15), block ∈ blocks ∧ pair ⊆ support \ block)
    (_hfirstMem : first ∈ blocks) (_hsecondMem : second ∈ blocks)
    (_hthirdMem : third ∈ blocks)
    (hfirstKilled : ¬first ⊆ (support.erase x).erase y)
    (hsecondKilled : ¬second ⊆ (support.erase x).erase y)
    (hthirdKilled : ¬third ⊆ (support.erase x).erase y)
    (hwitness : Fin15ThreeExteriorDoubleEraseWitness chi support q r s x y) :
    ((∃ residue : Finset (Fin 15),
        residue ⊆ (support.erase x).erase y ∧ residue.card = 2 ∧
          IsStrongPolygonSet chi (insert q (insert r (insert s residue)))) ∨
      (∃ residue : Finset (Fin 15),
        residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
          IsStrongPolygonSet chi (insert q (insert r residue))) ∨
      (∃ residue : Finset (Fin 15),
        residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
          IsStrongPolygonSet chi (insert q (insert s residue))) ∨
      ∃ residue : Finset (Fin 15),
        residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
          IsStrongPolygonSet chi (insert r (insert s residue))) ∨
    ((∃ alternative : Finset (Fin 15),
        alternative ⊆ (support.erase x).erase y ∧ alternative.card = 4 ∧
        IsStrongPolygonSet chi (insert q alternative) ∧ alternative ≠ first ∧
        (alternative ∈ blocks ∨
          ∃ block ∈ blocks,
            (alternative ∩ block).card = 3 ∧
            (alternative \ block).card = 1 ∧
            (block \ alternative).card = 1)) ∨
      (∃ alternative : Finset (Fin 15),
        alternative ⊆ (support.erase x).erase y ∧ alternative.card = 4 ∧
        IsStrongPolygonSet chi (insert r alternative) ∧ alternative ≠ second ∧
        (alternative ∈ blocks ∨
          ∃ block ∈ blocks,
            (alternative ∩ block).card = 3 ∧
            (alternative \ block).card = 1 ∧
            (block \ alternative).card = 1)) ∨
      ∃ alternative : Finset (Fin 15),
        alternative ⊆ (support.erase x).erase y ∧ alternative.card = 4 ∧
        IsStrongPolygonSet chi (insert s alternative) ∧ alternative ≠ third ∧
        (alternative ∈ blocks ∨
          ∃ block ∈ blocks,
            (alternative ∩ block).card = 3 ∧
            (alternative \ block).card = 1 ∧
            (block \ alternative).card = 1)) := by
  rcases hwitness with hthree | hqr | hqs | hrs | hq | hr | hs
  · exact Or.inl (Or.inl hthree)
  · exact Or.inl (Or.inr (Or.inl hqr))
  · exact Or.inl (Or.inr (Or.inr (Or.inl hqs)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr hrs)))
  · apply Or.inr
    apply Or.inl
    obtain ⟨alternative, hsub, hcard, hstrong⟩ := hq
    have hne : alternative ≠ first := by
      intro heq
      apply hfirstKilled
      simpa [← heq] using hsub
    exact ⟨alternative, hsub, hcard, hstrong, hne,
      fano_fourBlock_mem_or_singleExchange support blocks alternative
        hsupportCard hblockSub hblockCard hfano
          (hsub.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))) hcard⟩
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    obtain ⟨alternative, hsub, hcard, hstrong⟩ := hr
    have hne : alternative ≠ second := by
      intro heq
      apply hsecondKilled
      simpa [← heq] using hsub
    exact ⟨alternative, hsub, hcard, hstrong, hne,
      fano_fourBlock_mem_or_singleExchange support blocks alternative
        hsupportCard hblockSub hblockCard hfano
          (hsub.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))) hcard⟩
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    obtain ⟨alternative, hsub, hcard, hstrong⟩ := hs
    have hne : alternative ≠ third := by
      intro heq
      apply hthirdKilled
      simpa [← heq] using hsub
    exact ⟨alternative, hsub, hcard, hstrong, hne,
      fano_fourBlock_mem_or_singleExchange support blocks alternative
        hsupportCard hblockSub hblockCard hfano
          (hsub.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))) hcard⟩

/-- The non-premise-inert residue attached directly to a classified
multiplicity-three block: for every ordered pair of distinct erased block
vertices, maximality forces a seven-way classified witness meeting the
original block in at most two vertices. -/
theorem fin15_threeFiber_doubleBaseErase_forcedWitness
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    {support : Finset (Fin 15)}
    {anchor : Fin 15 → Finset (Fin 15)}
    (hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (hsupportCard : support.card = 7)
    (hanchorData : ∀ vertex ∈ Finset.univ \ support,
      anchor vertex ⊆ support ∧
        (anchor vertex).card = 4 ∧
        IsStrongPolygonSet chi (insert vertex (anchor vertex)))
    (index : Fin 8 ≃ {vertex // vertex ∈ Finset.univ \ support})
    (block : Finset (Fin 15))
    (hthree : 3 ≤ (Finset.univ.filter fun i : Fin 8 ↦ anchor (index i).1 = block).card) :
    ∃ q ∈ Finset.univ \ support,
      ∃ r ∈ Finset.univ \ support,
        ∃ s ∈ Finset.univ \ support,
          q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
          anchor q = block ∧ anchor r = block ∧ anchor s = block ∧
          Fin15SharedPairDefect chi block q r ∧
          Fin15SharedPairDefect chi block q s ∧
          Fin15SharedPairDefect chi block r s ∧
          ∀ c ∈ block, ∀ d ∈ block, c ≠ d →
            ∃ polygon : Finset (Fin 15),
              polygon ⊆
                insert q (insert r (insert s ((support.erase c).erase d))) ∧
              polygon.card = 5 ∧
              IsStrongPolygonSet chi polygon ∧
              Fin15ThreeExteriorWitnessPattern polygon q r s ∧
              Fin15ThreeExteriorDoubleEraseWitness chi support q r s c d ∧
              (polygon ∩ block).card ≤ 2 := by
  obtain ⟨q, hq, r, hr, s, hs, hqr, hqs, hrs,
      hqBlock, hrBlock, hsBlock, hqrDefect, hqsDefect, hrsDefect⟩ :=
    fin15_threeFiber_pairDefects chi hone hnoStrong hanchorData index block hthree
  have hqData := hanchorData q hq
  have hblockSub : block ⊆ support := by simpa [hqBlock] using hqData.1
  have hblockCard : block.card = 4 := by simpa [hqBlock] using hqData.2.1
  refine ⟨q, hq, r, hr, s, hs, hqr, hqs, hrs,
    hqBlock, hrBlock, hsBlock, hqrDefect, hqsDefect, hrsDefect, ?_⟩
  intro c hc d hd hcd
  exact fin15_threeExterior_doubleBaseErase_forcedWitness_exact
    chi hmaximum hsupportCard hblockSub hblockCard hq hr hs hqr hqs hrs hc hd hcd

/-- The exact shared-anchor hypotheses force a two-base single-end defect and
also supply a third exterior strong extension.  This is the narrow global
obstruction left before the frozen raw `False` endpoint. -/
theorem fin15ExteriorSystem_sharedAnchor_third_defect
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    {support : Finset (Fin 15)}
    {anchor : Fin 15 → Finset (Fin 15)}
    (_hmaximum : IsMaximumPredecessorFreeSupport chi 6 support)
    (_hsupportCard : support.card = 7)
    (houtsideCard : (Finset.univ \ support).card = 8)
    (hanchorData : ∀ vertex ∈ Finset.univ \ support,
      anchor vertex ⊆ support ∧
        (anchor vertex).card = 4 ∧
        IsStrongPolygonSet chi (insert vertex (anchor vertex)))
    {q r : Fin 15}
    (hq : q ∈ Finset.univ \ support)
    (hr : r ∈ Finset.univ \ support)
    (hqr : q ≠ r)
    (hshared : anchor q = anchor r) :
    ∃ s ∈ Finset.univ \ support,
      s ≠ q ∧ s ≠ r ∧
        anchor s ⊆ support ∧
        (anchor s).card = 4 ∧
        IsStrongPolygonSet chi (insert s (anchor s)) ∧
        ∃ i j k l : Fin 15, ∃ (hij : i < j) (hjk : j < k) (hkl : k < l),
          i ∈ insert q (insert r (anchor q)) ∧
          j ∈ insert q (insert r (anchor q)) ∧
          k ∈ insert q (insert r (anchor q)) ∧
          l ∈ insert q (insert r (anchor q)) ∧
          (q = i ∨ q = j ∨ q = k ∨ q = l) ∧
          (r = i ∨ r = j ∨ r = k ∨ r = l) ∧
          (({i, j, k, l} : Finset (Fin 15)) ∩ anchor q).card = 2 ∧
          ((chi ⟨i, j, k, hij, hjk⟩ =
                chi ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
              chi ⟨i, k, l, hij.trans hjk, hkl⟩ ≠
                chi ⟨j, k, l, hjk, hkl⟩) ∨
            (chi ⟨i, j, k, hij, hjk⟩ ≠
                chi ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
              chi ⟨i, k, l, hij.trans hjk, hkl⟩ =
                chi ⟨j, k, l, hjk, hkl⟩)) := by
  obtain ⟨s, hs, hsq, hsr⟩ := exists_third_of_mem_of_mem_of_card_eight
    houtsideCard hq hr hqr
  have hqData := hanchorData q hq
  have hrData := hanchorData r hr
  have hsData := hanchorData s hs
  have hrStrong : IsStrongPolygonSet chi (insert r (anchor q)) := by
    simpa [hshared] using hrData.2.2
  obtain ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl,
      hqOccurs, hrOccurs, htwoBase, hsingle⟩ :=
    predecessorHalfFin15_sharedAnchor_singleEndDefect_twoBase
      chi hone hnoStrong hqData.1 hqData.2.1 hq hr hqr hqData.2.2 hrStrong
  exact ⟨s, hs, hsq, hsr, hsData.1, hsData.2.1, hsData.2.2,
    i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl,
    hqOccurs, hrOccurs, htwoBase, hsingle⟩

end ErdosSzekeres

end
