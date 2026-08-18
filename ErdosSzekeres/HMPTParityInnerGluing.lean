module

public import ErdosSzekeres.HMPTHorizontalChainConvexity
public import ErdosSzekeres.HMPTCyclicHorizontalSeparation

@[expose] public section

/-!
# Cyclic gluing of HMPT inner horizontal chains

For either parity of the cyclic spike family, every stored inner horizontal
chain is glued on the original carrier.  Nontrivial local chains supply a
supporting neighbor at each vertex, while singleton chains use the strict
spike-base separator.
-/

namespace ErdosSzekeres

noncomputable section

private theorem hmptGluing_orientation_finset_affine
    (a b : Point 2) (t : Finset (Point 2)) (w : Point 2 → ℝ)
    (hw : ∑ z ∈ t, w z = 1) :
    orientation a b (∑ z ∈ t, w z • z) =
      ∑ z ∈ t, w z * orientation a b z := by
  let linearPart : Point 2 → ℝ := fun z ↦
    (b 0 - a 0) * z 1 - (b 1 - a 1) * z 0
  have horient (z : Point 2) :
      orientation a b z = linearPart z - linearPart a := by
    simp only [orientation, linearPart]
    ring
  rw [horient]
  have hlinear :
      linearPart (∑ z ∈ t, w z • z) =
        ∑ z ∈ t, w z * linearPart z := by
    simp only [linearPart, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hlinear]
  simp_rw [horient, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hw, one_mul]

private theorem inConvexPosition_of_mixed_vertex_certificates_g4
    {s : Finset (Point 2)}
    (hcert : ∀ ⦃p : Point 2⦄, p ∈ s →
      (∃ q ∈ s, ∃ common : Point 2,
          p ≠ q ∧ orientation p q common ≠ 0 ∧
            ∀ ⦃z : Point 2⦄, z ∈ s → z ≠ p → z ≠ q →
              SameStrictSide p q common z) ∨
        (∃ a b : Point 2,
          orientation a b p ≠ 0 ∧
            ∀ ⦃z : Point 2⦄, z ∈ s → z ≠ p →
              orientation a b p * orientation a b z < 0)) :
    InConvexPosition s := by
  classical
  intro p hp hphull
  obtain ⟨w, hwNonneg, hwSum, hwPoint⟩ :=
    Finset.mem_convexHull'.mp hphull
  rcases hcert hp with hedge | hstrict
  · obtain ⟨q, hq, common, hpq, hcommonNe, hall⟩ := hedge
    have hqErase : q ∈ s.erase p :=
      Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
    have haffine := hmptGluing_orientation_finset_affine
      p q (s.erase p) w hwSum
    rw [hwPoint, orientation_first_eq_third] at haffine
    have finish
        (hweightZero : ∀ z ∈ s.erase p, z ≠ q → w z = 0) : False := by
      have hsumSingle : ∑ z ∈ s.erase p, w z = w q := by
        apply Finset.sum_eq_single q
        · intro z hz hzq
          exact hweightZero z hz hzq
        · simp [hqErase]
      have hwq : w q = 1 := by
        rw [← hsumSingle]
        exact hwSum
      have hpointSingle : ∑ z ∈ s.erase p, w z • z = w q • q := by
        apply Finset.sum_eq_single q
        · intro z hz hzq
          rw [hweightZero z hz hzq, zero_smul]
        · simp [hqErase]
      rw [hpointSingle, hwq, one_smul] at hwPoint
      exact hpq hwPoint.symm
    rcases lt_or_gt_of_ne hcommonNe with hcommonNeg | hcommonPos
    · have hterm : ∀ z ∈ s.erase p,
          w z * orientation p q z ≤ 0 := by
        intro z hz
        by_cases hzq : z = q
        · subst z
          simp
        · have hzSide := hall (Finset.mem_of_mem_erase hz)
            (Finset.ne_of_mem_erase hz) hzq
          have hzNeg : orientation p q z < 0 := by
            rcases hzSide with ⟨-, hzNeg⟩ | ⟨hcommonPos', -⟩
            · exact hzNeg
            · linarith
          exact mul_nonpos_of_nonneg_of_nonpos (hwNonneg z hz) hzNeg.le
      have hsumZero :
          ∑ z ∈ s.erase p, w z * orientation p q z = 0 :=
        haffine.symm
      have hzero := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hsumZero
      apply finish
      intro z hz hzq
      have hzSide := hall (Finset.mem_of_mem_erase hz)
        (Finset.ne_of_mem_erase hz) hzq
      have hzNeg : orientation p q z < 0 := by
        rcases hzSide with ⟨-, hzNeg⟩ | ⟨hcommonPos', -⟩
        · exact hzNeg
        · linarith
      rcases mul_eq_zero.mp (hzero z hz) with hwz | hz0
      · exact hwz
      · exact (ne_of_lt hzNeg hz0).elim
    · have hterm : ∀ z ∈ s.erase p,
          0 ≤ w z * orientation p q z := by
        intro z hz
        by_cases hzq : z = q
        · subst z
          simp
        · have hzSide := hall (Finset.mem_of_mem_erase hz)
            (Finset.ne_of_mem_erase hz) hzq
          have hzPos : 0 < orientation p q z := by
            rcases hzSide with ⟨hcommonNeg', -⟩ | ⟨-, hzPos⟩
            · linarith
            · exact hzPos
          exact mul_nonneg (hwNonneg z hz) hzPos.le
      have hsumZero :
          ∑ z ∈ s.erase p, w z * orientation p q z = 0 :=
        haffine.symm
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsumZero
      apply finish
      intro z hz hzq
      have hzSide := hall (Finset.mem_of_mem_erase hz)
        (Finset.ne_of_mem_erase hz) hzq
      have hzPos : 0 < orientation p q z := by
        rcases hzSide with ⟨hcommonNeg', -⟩ | ⟨-, hzPos⟩
        · linarith
        · exact hzPos
      rcases mul_eq_zero.mp (hzero z hz) with hwz | hz0
      · exact hwz
      · exact (ne_of_gt hzPos hz0).elim
  · obtain ⟨a, b, hpLine, hall⟩ := hstrict
    have haffine := hmptGluing_orientation_finset_affine
      a b (s.erase p) w hwSum
    rw [hwPoint] at haffine
    rcases lt_or_gt_of_ne hpLine with hpNeg | hpPos
    · have hterm : ∀ z ∈ s.erase p,
          0 ≤ w z * orientation a b z := by
        intro z hz
        have hzProd := hall (Finset.mem_of_mem_erase hz)
          (Finset.ne_of_mem_erase hz)
        have hzPos : 0 < orientation a b z := by nlinarith
        exact mul_nonneg (hwNonneg z hz) hzPos.le
      have hsumNonneg :
          0 ≤ ∑ z ∈ s.erase p, w z * orientation a b z :=
        Finset.sum_nonneg hterm
      linarith
    · have hterm : ∀ z ∈ s.erase p,
          w z * orientation a b z ≤ 0 := by
        intro z hz
        have hzProd := hall (Finset.mem_of_mem_erase hz)
          (Finset.ne_of_mem_erase hz)
        have hzNeg : orientation a b z < 0 := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos (hwNonneg z hz) hzNeg.le
      have hsumNonpos :
          ∑ z ∈ s.erase p, w z * orientation a b z ≤ 0 :=
        Finset.sum_nonpos hterm
      linarith

private theorem hmptGluing_crossed_segments_orientation_neg
    (outerLeft outerRight p q : Point 2)
    (hp : 0 < orientation outerLeft outerRight p)
    (hq : 0 < orientation outerLeft outerRight q)
    (hleft : orientation outerLeft p q ≠ 0)
    (hright : orientation outerRight p q ≠ 0)
    (hcrossed : Set.Nonempty
      (convexHull ℝ ({outerLeft, q} : Set (Point 2)) ∩
        convexHull ℝ ({outerRight, p} : Set (Point 2)))) :
    orientation outerLeft p q < 0 ∧
      orientation outerRight p q < 0 := by
  rcases hcrossed with ⟨x, hxLeft, hxRight⟩
  rw [convexHull_pair, segment_eq_image] at hxLeft hxRight
  rcases hxLeft with ⟨t, ht, htx⟩
  rcases hxRight with ⟨u, hu, hux⟩
  have hAqx : orientation outerLeft q x = 0 := by
    rw [← htx, orientation_affine_combo_right outerLeft q outerLeft q
      (1 - t) t (by ring)]
    simp
  have hAqxCombo :
      orientation outerLeft q x =
        (1 - u) * orientation outerLeft q outerRight +
          u * orientation outerLeft q p := by
    rw [← hux, orientation_affine_combo_right outerLeft q outerRight p
      (1 - u) u (by ring)]
  rw [orientation_swap_last outerLeft outerRight q,
    orientation_swap_last outerLeft p q] at hAqxCombo
  have heqLeft :
      (1 - u) * orientation outerLeft outerRight q +
        u * orientation outerLeft p q = 0 := by
    nlinarith
  have huPos : 0 < u := by
    by_contra hnot
    have huZero : u = 0 := le_antisymm (le_of_not_gt hnot) hu.1
    rw [huZero] at heqLeft
    simp at heqLeft
    linarith
  have hleftWeak : orientation outerLeft p q ≤ 0 := by
    nlinarith [hu.2]
  have hDpx : orientation outerRight p x = 0 := by
    rw [← hux, orientation_affine_combo_right outerRight p outerRight p
      (1 - u) u (by ring)]
    simp
  have hDpxCombo :
      orientation outerRight p x =
        (1 - t) * orientation outerRight p outerLeft +
          t * orientation outerRight p q := by
    rw [← htx, orientation_affine_combo_right outerRight p outerLeft q
      (1 - t) t (by ring)]
  rw [orientation_cyclic outerLeft outerRight p] at hDpxCombo
  have heqRight :
      (1 - t) * orientation outerLeft outerRight p +
        t * orientation outerRight p q = 0 := by
    nlinarith
  have htPos : 0 < t := by
    by_contra hnot
    have htZero : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1
    rw [htZero] at heqRight
    simp at heqRight
    linarith
  have hrightWeak : orientation outerRight p q ≤ 0 := by
    nlinarith [ht.2]
  exact ⟨lt_of_le_of_ne hleftWeak hleft,
    lt_of_le_of_ne hrightWeak hright⟩

private structure HMPTOrderedInnerPointG4
    {s : Finset (Point 2)} (selected : Finset (↥s)) where
  val : ↥selected
  deriving Fintype

private def hmptOrderedInnerPointEquivG4
    {s : Finset (Point 2)} (selected : Finset (↥s)) :
    HMPTOrderedInnerPointG4 selected ≃ ↥selected where
  toFun p := p.val
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem horizontalLT_trans_g4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q r : ↥s)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1)
    (hqr : HMPTSpikeHorizontalLT outerLeft outerRight q.1 r.1) :
    HMPTSpikeHorizontalLT outerLeft outerRight p.1 r.1 := by
  have hpair := h.toHMPTSpikeOrderPair
  rcases hpair.horizontal_trans p q r (Or.inr hpq) (Or.inr hqr) with
    hpr | hpr
  · exfalso
    apply hqr.1
    have hrq : HMPTSpikeHorizontalLE outerLeft outerRight r.1 q.1 := by
      rw [← hpr]
      exact Or.inr hpq
    have hqrEq := hpair.horizontal_antisymm q r (Or.inr hqr) hrq
    exact congrArg Subtype.val hqrEq
  · exact hpr

private theorem selected_horizontalLT_isStrictTotal_g4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalProfile : HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s)
    (selected : Finset (↥s))
    (hselected : selected ⊆ verticalProfile.horizontalChain) :
    IsStrictTotalOrder (HMPTOrderedInnerPointG4 selected)
      (fun p q ↦ HMPTSpikeHorizontalLT
        outerLeft outerRight p.val.1.1 q.val.1.1) where
  irrefl p hp := hp.1 rfl
  trans p q r hpq hqr :=
    h.horizontalLT_trans_g4 p.val.1 q.val.1 r.val.1 hpq hqr
  trichotomous p q hpq hqp := by
    by_contra hpqNe
    have hpqVal : p.val.1 ≠ q.val.1 := by
      intro heq
      apply hpqNe
      apply (hmptOrderedInnerPointEquivG4 selected).injective
      exact Subtype.ext heq
    rcases verticalProfile.horizontalMaximum.1
        (hselected p.val.property) (hselected q.val.property) hpqVal with
      hpqLE | hqpLE
    · rcases hpqLE with heq | hlt
      · exact hpqVal (Subtype.ext heq)
      · exact hpq hlt
    · rcases hqpLE with heq | hlt
      · exact hpqVal (Subtype.ext heq.symm)
      · exact hqp hlt

private theorem horizontalLT_orientation_neg_g4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (p q : ↥s)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1 q.1) :
    orientation outerLeft p.1 q.1 < 0 ∧
      orientation outerRight p.1 q.1 < 0 := by
  have hpBase : 0 < orientation outerLeft outerRight p.1 :=
    h.base_orientation_pos p
  have hqBase : 0 < orientation outerLeft outerRight q.1 :=
    h.base_orientation_pos q
  have houterLeftP : outerLeft ≠ p.1 := by
    intro heq
    rw [← heq] at hpBase
    simp at hpBase
  have houterLeftQ : outerLeft ≠ q.1 := by
    intro heq
    rw [← heq] at hqBase
    simp at hqBase
  have houterRightP : outerRight ≠ p.1 := by
    intro heq
    rw [← heq] at hpBase
    simp at hpBase
  have houterRightQ : outerRight ≠ q.1 := by
    intro heq
    rw [← heq] at hqBase
    simp at hqBase
  have hleft : orientation outerLeft p.1 q.1 ≠ 0 :=
    h.generalPosition (by simp) (by simp [p.property])
      (by simp [q.property]) houterLeftP houterLeftQ hpq.1
  have hright : orientation outerRight p.1 q.1 ≠ 0 :=
    h.generalPosition (by simp) (by simp [p.property])
      (by simp [q.property]) houterRightP houterRightQ hpq.1
  exact hmptGluing_crossed_segments_orientation_neg
    outerLeft outerRight p.1 q.1 hpBase hqBase hleft hright hpq.2

private theorem ordered_inner_triple_orientation_neg_g4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    {selected : Finset (↥s)}
    (hliteral : ∀ triple : Finset (↥s), triple ⊆ selected →
      triple.card = 3 →
        InConvexPosition
          (insert outerLeft (insert outerRight (hmptChainPoints triple))))
    (p q r : ↥selected)
    (hpq : HMPTSpikeHorizontalLT outerLeft outerRight p.1.1 q.1.1)
    (hqr : HMPTSpikeHorizontalLT outerLeft outerRight q.1.1 r.1.1) :
    orientation p.1.1 q.1.1 r.1.1 < 0 := by
  let triple : Finset (↥s) := {p.1, q.1, r.1}
  have hpr := h.horizontalLT_trans_g4 p.1 q.1 r.1 hpq hqr
  have htripleSubset : triple ⊆ selected := by
    intro x hx
    simp only [triple, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact p.property
    · exact q.property
    · exact r.property
  have htripleCard : triple.card = 3 := by
    have hpq' : p.1 ≠ q.1 := fun heq ↦
      hpq.1 (congrArg Subtype.val heq)
    have hpr' : p.1 ≠ r.1 := fun heq ↦
      hpr.1 (congrArg Subtype.val heq)
    have hqr' : q.1 ≠ r.1 := fun heq ↦
      hqr.1 (congrArg Subtype.val heq)
    simp [triple, hpq', hpr', hqr']
  have hconvex : InConvexPosition
      {outerLeft, outerRight, p.1.1, q.1.1, r.1.1} := by
    simpa [triple, hmptChainPoints] using
      hliteral triple htripleSubset htripleCard
  have hright := (h.hmptHorizontalTripleGeometry.semantics
    p.1 q.1 r.1 hpq hqr).1.mpr hconvex
  simpa [hmptHorizontalTripleColor] using hright

private theorem innerChain_vertex_support_g4
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalProfile : HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s)
    (horizontalProfile : HMPTHorizontalProfile
      outerLeft rightAnchor leftAnchor outerRight s verticalProfile)
    (hcard : 2 ≤ horizontalProfile.innerChain.card)
    {p : Point 2} (hp : p ∈ hmptChainPoints horizontalProfile.innerChain) :
    ∃ q ∈ hmptChainPoints horizontalProfile.innerChain,
      p ≠ q ∧
        (HMPTSpikeHorizontalLT outerLeft outerRight p q ∨
          HMPTSpikeHorizontalLT outerLeft outerRight q p) ∧
        SameStrictSide p q outerLeft outerRight ∧
        ∀ ⦃z : Point 2⦄,
          z ∈ hmptChainPoints horizontalProfile.innerChain →
          z ≠ p → z ≠ q → SameStrictSide p q outerLeft z := by
  classical
  rcases Finset.mem_map.mp hp with ⟨p0, hp0, rfl⟩
  let selected := horizontalProfile.innerChain
  let horizontalLT : HMPTOrderedInnerPointG4 selected →
      HMPTOrderedInnerPointG4 selected → Prop :=
    fun x y ↦ HMPTSpikeHorizontalLT
      outerLeft outerRight x.val.1.1 y.val.1.1
  letI : DecidableRel horizontalLT := Classical.decRel _
  letI : IsStrictTotalOrder
      (HMPTOrderedInnerPointG4 selected) horizontalLT :=
    h.selected_horizontalLT_isStrictTotal_g4 verticalProfile selected
      horizontalProfile.innerMaximum.1.1
  letI : LinearOrder (HMPTOrderedInnerPointG4 selected) :=
    linearOrderOfSTO horizontalLT
  have hunivCard :
      (Finset.univ : Finset (HMPTOrderedInnerPointG4 selected)).card =
        selected.card := by
    simp [Fintype.card_congr (hmptOrderedInnerPointEquivG4 selected)]
  let e : Fin selected.card ↪o HMPTOrderedInnerPointG4 selected :=
    (Finset.univ : Finset (HMPTOrderedInnerPointG4 selected)).orderEmbOfFin
      hunivCard
  let pW : HMPTOrderedInnerPointG4 selected := ⟨⟨p0, hp0⟩⟩
  have hpRange : pW ∈ Set.range e := by
    rw [Finset.range_orderEmbOfFin
      (Finset.univ : Finset (HMPTOrderedInnerPointG4 selected)) hunivCard]
    simp
  obtain ⟨k, hk⟩ := hpRange
  by_cases hk0 : k.val = 0
  · let one : Fin selected.card := ⟨1, by simpa [selected] using hcard⟩
    let qW := e one
    let q : Point 2 := qW.val.1.1
    have hkOne : k < one := by
      apply Fin.mk_lt_mk.mpr
      simpa [one] using hk0
    have hpqOrder : horizontalLT pW qW := by
      have hmono := e.strictMono hkOne
      rw [hk] at hmono
      exact hmono
    have hqMem : q ∈ hmptChainPoints horizontalProfile.innerChain := by
      apply Finset.mem_map.mpr
      exact ⟨qW.val.1, qW.val.property, rfl⟩
    have hpqNe : p0.1 ≠ q := hpqOrder.1
    have hpqSigns := h.horizontalLT_orientation_neg_g4 p0 qW.val.1 hpqOrder
    refine ⟨q, hqMem, hpqNe, Or.inl hpqOrder,
      Or.inl ⟨?_, ?_⟩, ?_⟩
    · change orientation p0.1 q outerLeft < 0
      rw [orientation_cyclic outerLeft p0.1 q]
      simpa [q] using hpqSigns.1
    · change orientation p0.1 q outerRight < 0
      rw [orientation_cyclic outerRight p0.1 q]
      simpa [q] using hpqSigns.2
    · intro z hz hzp hzq
      rcases Finset.mem_map.mp hz with ⟨z0, hz0, rfl⟩
      let zW : HMPTOrderedInnerPointG4 selected := ⟨⟨z0, hz0⟩⟩
      have hzRange : zW ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin
          (Finset.univ : Finset (HMPTOrderedInnerPointG4 selected)) hunivCard]
        simp
      obtain ⟨l, hl⟩ := hzRange
      have hlk : l ≠ k := by
        intro hlk
        apply hzp
        have : zW = pW := by rw [← hl, ← hk, hlk]
        exact congrArg (fun x ↦ x.val.1.1) this
      have hlOne : l ≠ one := by
        intro hlOne
        apply hzq
        have : zW = qW := by rw [← hl, hlOne]
        exact congrArg (fun x ↦ x.val.1.1) this
      have honeL : one < l := by
        apply Fin.mk_lt_mk.mpr
        have hl0 : l.val ≠ 0 := by
          intro hl0
          apply hlk
          apply Fin.ext
          omega
        have hl1 : l.val ≠ 1 := by
          intro hl1
          apply hlOne
          apply Fin.ext
          simpa [one] using hl1
        omega
      have hqzOrder : horizontalLT qW zW := by
        have hmono := e.strictMono honeL
        rw [hl] at hmono
        exact hmono
      have hzNeg := h.ordered_inner_triple_orientation_neg_g4
        horizontalProfile.innerMaximum.1.2 pW.val qW.val zW.val
        hpqOrder hqzOrder
      exact Or.inl ⟨by
        change orientation p0.1 q outerLeft < 0
        rw [orientation_cyclic outerLeft p0.1 q]
        simpa [q] using hpqSigns.1, hzNeg⟩
  · have hkPos : 0 < k.val := by omega
    let previous : Fin selected.card := ⟨k.val - 1, by omega⟩
    let qW := e previous
    let q : Point 2 := qW.val.1.1
    have hPrevK : previous < k := by
      apply Fin.mk_lt_mk.mpr
      change k.val - 1 < k.val
      omega
    have hqpOrder : horizontalLT qW pW := by
      have hmono := e.strictMono hPrevK
      rw [hk] at hmono
      exact hmono
    have hqMem : q ∈ hmptChainPoints horizontalProfile.innerChain := by
      apply Finset.mem_map.mpr
      exact ⟨qW.val.1, qW.val.property, rfl⟩
    have hpqNe : p0.1 ≠ q := hqpOrder.1.symm
    have hqpSigns := h.horizontalLT_orientation_neg_g4 qW.val.1 p0 hqpOrder
    refine ⟨q, hqMem, hpqNe, Or.inr hqpOrder,
      Or.inr ⟨?_, ?_⟩, ?_⟩
    · change 0 < orientation p0.1 q outerLeft
      rw [orientation_cyclic outerLeft p0.1 q,
        orientation_swap_last outerLeft q p0.1]
      have := hqpSigns.1
      simpa [q] using neg_pos.mpr this
    · change 0 < orientation p0.1 q outerRight
      rw [orientation_cyclic outerRight p0.1 q,
        orientation_swap_last outerRight q p0.1]
      have := hqpSigns.2
      simpa [q] using neg_pos.mpr this
    · intro z hz hzp hzq
      rcases Finset.mem_map.mp hz with ⟨z0, hz0, rfl⟩
      let zW : HMPTOrderedInnerPointG4 selected := ⟨⟨z0, hz0⟩⟩
      have hzRange : zW ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin
          (Finset.univ : Finset (HMPTOrderedInnerPointG4 selected)) hunivCard]
        simp
      obtain ⟨l, hl⟩ := hzRange
      have hlk : l ≠ k := by
        intro hlk
        apply hzp
        have : zW = pW := by rw [← hl, ← hk, hlk]
        exact congrArg (fun x ↦ x.val.1.1) this
      have hlPrev : l ≠ previous := by
        intro hlPrev
        apply hzq
        have : zW = qW := by rw [← hl, hlPrev]
        exact congrArg (fun x ↦ x.val.1.1) this
      have hsplit : l < previous ∨ k < l := by
        rcases lt_trichotomy l previous with hlp | hlp | hpl
        · exact Or.inl hlp
        · exact (hlPrev hlp).elim
        · rcases lt_trichotomy k l with hkl | hkl | hlk'
          · exact Or.inr hkl
          · exact (hlk hkl.symm).elim
          · have hvals : l.val < k.val - 1 := by
              have := Fin.mk_lt_mk.mp hlk'
              have hp := Fin.mk_lt_mk.mp hpl
              omega
            exact Or.inl (Fin.mk_lt_mk.mpr hvals)
      have hzPos : 0 < orientation p0.1 q z0.1 := by
        rcases hsplit with hlPrevOrder | hkL
        · have hzqOrder : horizontalLT zW qW := by
            have hmono := e.strictMono hlPrevOrder
            rw [hl] at hmono
            exact hmono
          have hzqp := h.ordered_inner_triple_orientation_neg_g4
            horizontalProfile.innerMaximum.1.2 zW.val qW.val pW.val
            hzqOrder hqpOrder
          have hreverse :
              orientation p0.1 q z0.1 =
                -orientation z0.1 q p0.1 := by
            simp only [orientation]
            ring
          rw [hreverse]
          linarith
        · have hpzOrder : horizontalLT pW zW := by
            have hmono := e.strictMono hkL
            rw [hk, hl] at hmono
            exact hmono
          have hqpz := h.ordered_inner_triple_orientation_neg_g4
            horizontalProfile.innerMaximum.1.2 qW.val pW.val zW.val
            hqpOrder hpzOrder
          rw [orientation_swap q p0.1 z0.1]
          linarith
      exact Or.inr ⟨by
        change 0 < orientation p0.1 q outerLeft
        rw [orientation_cyclic outerLeft p0.1 q,
          orientation_swap_last outerLeft q p0.1]
        have := hqpSigns.1
        simpa [q] using neg_pos.mpr this, hzPos⟩

end SukRegionGeometry

namespace PorValtrSupportProductData

/-- For either parity, the union of the exact inner chains attached to one
cyclic H2/H3 profile family is in convex position on the original carrier. -/
theorem hmptParityInnerUnion_convex
    {P : Finset (Point 2)} {r : ℕ}
    (h : PorValtrSupportProductData P r)
    (hr : 3 ≤ r)
    (hgp : InGeneralPosition P)
    (verticalProfile : ∀ i : Fin (2 * r),
      HMPTVerticalProfile
        (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i))
    (horizontalProfile : ∀ i : Fin (2 * r),
      HMPTHorizontalProfile
        (h.hmptAnchor i 0) (h.hmptAnchor i 1)
        (h.hmptAnchor i 2) (h.hmptAnchor i 3) (h.hmptPool i)
        (verticalProfile i))
    (parity : Fin 2) :
    InConvexPosition
      ((Finset.univ.filter
        (fun i : Fin (2 * r) ↦ i.val % 2 = parity.val)).biUnion
          (fun i ↦ hmptChainPoints (horizontalProfile i).innerChain)) := by
  classical
  let selected := Finset.univ.filter
    (fun i : Fin (2 * r) ↦ i.val % 2 = parity.val)
  let cap : Fin (2 * r) → Finset (Point 2) := fun i ↦
    hmptChainPoints (horizontalProfile i).innerChain
  let union := selected.biUnion cap
  have geometry := h.toHMPTCyclicSpikeGeometry hr hgp
  have hcert : ∀ ⦃p : Point 2⦄, p ∈ union →
      (∃ q ∈ union, ∃ common : Point 2,
          p ≠ q ∧ orientation p q common ≠ 0 ∧
            ∀ ⦃z : Point 2⦄, z ∈ union → z ≠ p → z ≠ q →
              SameStrictSide p q common z) ∨
        (∃ a b : Point 2,
          orientation a b p ≠ 0 ∧
            ∀ ⦃z : Point 2⦄, z ∈ union → z ≠ p →
              orientation a b p * orientation a b z < 0) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    have hiParity : i.val % 2 = parity.val := by
      simpa [selected] using hi
    have hpiPool : p ∈ h.hmptPool i :=
      hmptChainPoints_subset (horizontalProfile i).innerChain hpi
    by_cases hlarge : 2 ≤ (horizontalProfile i).innerChain.card
    · obtain ⟨q, hqi, hpq, hcompare, hbase, hlocal⟩ :=
        (geometry.localRegion i).innerChain_vertex_support_g4
          (verticalProfile i) (horizontalProfile i) hlarge hpi
      have hqUnion : q ∈ union :=
        Finset.mem_biUnion.mpr ⟨i, hi, hqi⟩
      refine Or.inl ⟨q, hqUnion, h.hmptAnchor i 0, hpq, ?_, ?_⟩
      · rcases hbase with ⟨hneg, -⟩ | ⟨hpos, -⟩
        · exact ne_of_lt hneg
        · exact ne_of_gt hpos
      · intro z hz hzp hzq
        obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hz
        by_cases hij : i = j
        · subst j
          exact hlocal hzj hzp hzq
        · have hjParity : j.val % 2 = parity.val := by
            simpa [selected] using hj
          have hzPool : z ∈ h.hmptPool j :=
            hmptChainPoints_subset (horizontalProfile j).innerChain hzj
          exact h.horizontalPair_remote_sameStrictSide hr hgp i j
            (hiParity.trans hjParity.symm) hij hpiPool
            (hmptChainPoints_subset (horizontalProfile i).innerChain hqi)
            hzPool hcompare
    · have hsmall : (horizontalProfile i).innerChain.card ≤ 1 := by omega
      refine Or.inr ⟨h.hmptAnchor i 1, h.hmptAnchor i 2, ?_, ?_⟩
      · have hpBase := (geometry.localRegion i).region hpiPool |>.1
        exact ne_of_gt hpBase
      · intro z hz hzp
        obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hz
        have hjParity : j.val % 2 = parity.val := by
          simpa [selected] using hj
        by_cases hij : i = j
        · subst j
          exfalso
          apply hzp
          have hpointsSmall :
              (hmptChainPoints (horizontalProfile i).innerChain).card ≤ 1 := by
            simpa using hsmall
          exact (Finset.card_le_one.mp hpointsSmall p hpi z hzj).symm
        · have hzPool : z ∈ h.hmptPool j :=
            hmptChainPoints_subset (horizontalProfile j).innerChain hzj
          exact h.baseEdge_remote_oppositeSide hr hgp i j
            (hiParity.trans hjParity.symm) hij hpiPool hzPool
  change InConvexPosition union
  exact inConvexPosition_of_mixed_vertex_certificates_g4 hcert

end PorValtrSupportProductData

end

end ErdosSzekeres

end
