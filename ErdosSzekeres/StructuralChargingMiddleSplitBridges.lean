module

public import ErdosSzekeres.StructuralChargingMiddleSplitClasses

@[expose] public section

/-!
# Common bridge certificates for middle crossing failures

The nineteen normalized failure classes all force a four-vertex one-change
pattern with three consecutive equal colors. This file packages that common
output without forgetting that the probe is one vertex and the other three
vertices come from the reference strong six.
-/

namespace ErdosSzekeres

/-- A four-vertex bridge certificate through `q`. Exactly one vertex is the
probe by strict ordering and `q` occupies one of the four listed positions;
the other three listed vertices belong to `polygon`. The color sequence has
either a monochromatic head or a monochromatic tail of length three. -/
def HasMiddleFailureBridgeCertificate {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d),
    a ∈ insert q polygon ∧ b ∈ insert q polygon ∧
      c ∈ insert q polygon ∧ d ∈ insert q polygon ∧
      (a = q ∨ b = q ∨ c = q ∨ d = q) ∧
      ((χ ⟨a, b, c, hab, hbc⟩ = χ ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
          χ ⟨a, b, d, hab, hbc.trans hcd⟩ =
            χ ⟨a, c, d, hab.trans hbc, hcd⟩) ∨
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩ =
            χ ⟨a, c, d, hab.trans hbc, hcd⟩ ∧
          χ ⟨a, c, d, hab.trans hbc, hcd⟩ =
            χ ⟨b, c, d, hbc, hcd⟩))

/-- The interior subcase of a bridge certificate, where the probe is the
second or third vertex of the ordered four-set. -/
def HasInteriorMiddleFailureBridgeCertificate {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d),
    a ∈ insert q polygon ∧ b ∈ insert q polygon ∧
      c ∈ insert q polygon ∧ d ∈ insert q polygon ∧
      (b = q ∨ c = q) ∧
      ((χ ⟨a, b, c, hab, hbc⟩ = χ ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
          χ ⟨a, b, d, hab, hbc.trans hcd⟩ =
            χ ⟨a, c, d, hab.trans hbc, hcd⟩) ∨
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩ =
            χ ⟨a, c, d, hab.trans hbc, hcd⟩ ∧
          χ ⟨a, c, d, hab.trans hbc, hcd⟩ =
            χ ⟨b, c, d, hbc, hcd⟩))

/-- A probe is anchored on an ordered polygon frame when it lies in one of
the frame's two interior gaps and its outer-pair color equals the frame color. -/
def HasFrameAnchoredBridge {n : ℕ} (χ : TripleColoring n)
    (q x y z : Fin n) : Prop :=
  ((x < q ∧ q < y ∧ y < z) ∨ (x < y ∧ y < q ∧ q < z)) ∧
    CupCap.totalColor χ x q z = CupCap.totalColor χ x y z

/-- Constructor for the monochromatic-head form of the common certificate. -/
theorem middleFailureBridgeCertificate_of_head
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ insert q polygon) (hb : b ∈ insert q polygon)
    (hc : c ∈ insert q polygon) (hd : d ∈ insert q polygon)
    (hq : a = q ∨ b = q ∨ c = q ∨ d = q)
    (hfirst : χ ⟨a, b, c, hab, hbc⟩ =
      χ ⟨a, b, d, hab, hbc.trans hcd⟩)
    (hsecond : χ ⟨a, b, d, hab, hbc.trans hcd⟩ =
      χ ⟨a, c, d, hab.trans hbc, hcd⟩) :
    HasMiddleFailureBridgeCertificate χ polygon q := by
  exact ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hq,
    Or.inl ⟨hfirst, hsecond⟩⟩

/-- Constructor for the monochromatic-tail form of the common certificate. -/
theorem middleFailureBridgeCertificate_of_tail
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ insert q polygon) (hb : b ∈ insert q polygon)
    (hc : c ∈ insert q polygon) (hd : d ∈ insert q polygon)
    (hq : a = q ∨ b = q ∨ c = q ∨ d = q)
    (hfirst : χ ⟨a, b, d, hab, hbc.trans hcd⟩ =
      χ ⟨a, c, d, hab.trans hbc, hcd⟩)
    (hsecond : χ ⟨a, c, d, hab.trans hbc, hcd⟩ =
      χ ⟨b, c, d, hbc, hcd⟩) :
    HasMiddleFailureBridgeCertificate χ polygon q := by
  exact ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd, hq,
    Or.inr ⟨hfirst, hsecond⟩⟩

/-- A fresh-middle fan always produces an interior bridge certificate. -/
theorem freshMiddleFanVariation_has_interiorBridgeCertificate
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hpolygonSub : polygon ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hfan : HasFreshMiddleFanVariation χ polygon q) :
    HasInteriorMiddleFailureBridgeCertificate χ polygon q := by
  have insertMem {x : Fin n} (hx : x ∈ polygon) : x ∈ insert q polygon :=
    Finset.mem_insert_of_mem hx
  have hqInsert : q ∈ insert q polygon := Finset.mem_insert_self q polygon
  rcases freshMiddleFanVariation_has_oneSided_fan hfan with hearlier | hlater
  · obtain ⟨a, b, k, hab, haq, hbq, hqk, ha, hb, hk,
      hfirst, hsecond⟩ :=
      freshMiddleEarlierFan_forces_bridge_colors hpolygonSub hqAmbient
        hone hearlier
    exact ⟨a, b, q, k, hab, hbq, hqk, insertMem ha, insertMem hb,
      hqInsert, insertMem hk, Or.inr rfl,
      Or.inl ⟨hfirst.trans hsecond.symm, hsecond⟩⟩
  · obtain ⟨i, a, b, hiq, hqa, _hqb, hab, hi, ha, hb,
      hfirst, hsecond⟩ :=
      freshMiddleLaterFan_forces_bridge_colors hpolygonSub hqAmbient
        hone hlater
    exact ⟨i, q, a, b, hiq, hqa, hab, insertMem hi, hqInsert,
      insertMem ha, insertMem hb, Or.inl rfl,
      Or.inr ⟨hfirst.symm, hfirst.trans hsecond.symm⟩⟩

/-- The middle equality common to both bridge polarities anchors every
interior certificate to the color of its three polygon vertices. -/
theorem interiorBridgeCertificate_has_frameAnchor
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hcertificate : HasInteriorMiddleFailureBridgeCertificate χ polygon q) :
    ∃ x y z, x ∈ polygon ∧ y ∈ polygon ∧ z ∈ polygon ∧
      HasFrameAnchoredBridge χ q x y z := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc, hd,
    hbq | hcq, hcolors⟩ := hcertificate
  · subst b
    have memPolygon {u : Fin n} (hu : u ∈ insert q polygon)
        (huq : u ≠ q) : u ∈ polygon := by
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact (huq rfl).elim
      · exact hu
    have haPolygon := memPolygon ha (by omega)
    have hcPolygon := memPolygon hc (by omega)
    have hdPolygon := memPolygon hd (by omega)
    have hmiddle := hcolors.elim And.right And.left
    refine ⟨a, c, d, haPolygon, hcPolygon, hdPolygon,
      Or.inl ⟨hab, hbc, hcd⟩, ?_⟩
    rw [CupCap.totalColor_of_lt χ hab (hbc.trans hcd),
      CupCap.totalColor_of_lt χ (hab.trans hbc) hcd]
    exact hmiddle
  · subst c
    have memPolygon {u : Fin n} (hu : u ∈ insert q polygon)
        (huq : u ≠ q) : u ∈ polygon := by
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact (huq rfl).elim
      · exact hu
    have haPolygon := memPolygon ha (by omega)
    have hbPolygon := memPolygon hb (by omega)
    have hdPolygon := memPolygon hd (by omega)
    have hmiddle := hcolors.elim And.right And.left
    refine ⟨a, b, d, haPolygon, hbPolygon, hdPolygon,
      Or.inr ⟨hab, hbc, hcd⟩, ?_⟩
    rw [CupCap.totalColor_of_lt χ (hab.trans hbc) hcd,
      CupCap.totalColor_of_lt χ hab (hbc.trans hcd)]
    exact hmiddle.symm

/-- Two probes anchored on the same ordered polygon frame have the same
outer-pair color. Exhaustive five-vertex checking shows that no color on a
triple containing both probes follows from these hypotheses alone. -/
theorem frameAnchoredBridges_two_probe_agreement
    {n : ℕ} {χ : TripleColoring n} {q₁ q₂ x y z : Fin n}
    (hfirst : HasFrameAnchoredBridge χ q₁ x y z)
    (hsecond : HasFrameAnchoredBridge χ q₂ x y z) :
    CupCap.totalColor χ x q₁ z = CupCap.totalColor χ x q₂ z := by
  exact hfirst.2.trans hsecond.2.symm

/-- Fresh-middle failures are the normalized classes that always provide an
interior, frame-anchored bridge. -/
theorem freshMiddleFanVariation_has_frameAnchor
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hpolygonSub : polygon ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hfan : HasFreshMiddleFanVariation χ polygon q) :
    ∃ x y z, x ∈ polygon ∧ y ∈ polygon ∧ z ∈ polygon ∧
      HasFrameAnchoredBridge χ q x y z := by
  exact interiorBridgeCertificate_has_frameAnchor
    (freshMiddleFanVariation_has_interiorBridgeCertificate hpolygonSub
      hqAmbient hone hfan)

/-- Every one of the nineteen normalized classes produces the same bridge
certificate under the ambient one-change law. -/
theorem normalizedCutFailureClass_has_bridgeCertificate
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hcard : polygon.card = 6)
    (hpolygonSub : polygon ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hqPolygon : q ∉ polygon) (hone : OneChangeOn χ ambient)
    (c : NormalizedCutFailureClass)
    (hclass : RealizesNormalizedCutFailureClass χ polygon hcard q c) :
    HasMiddleFailureBridgeCertificate χ polygon q := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (s : Fin 6) : e s ∈ polygon := polygon.orderEmbOfFin_mem hcard s
  have insertMem {x : Fin n} (hx : x ∈ polygon) : x ∈ insert q polygon :=
    Finset.mem_insert_of_mem hx
  have hqInsert : q ∈ insert q polygon := Finset.mem_insert_self q polygon
  cases c with
  | leftAnomaly r =>
      change HasCanonicalLeftEndpointAnomalyAt χ polygon hcard q r at hclass
      let j := e (strongSixInternalIndex r)
      obtain ⟨hqj, hneq⟩ := hclass
      have hfirstj : e 0 < j := e.strictMono (by
        change 0 < r.val + 1
        omega)
      have hjlast : j < e 5 := e.strictMono (by
        change r.val + 1 < 5
        omega)
      have hqFirst : q ≠ e 0 := fun heq ↦ hqPolygon (heq ▸ heMem 0)
      rcases lt_or_gt_of_ne hqFirst with hqfirst | hfirstq
      · have hallowed := hone hqfirst hfirstj hjlast hqAmbient
          (hpolygonSub (heMem 0))
          (hpolygonSub (heMem (strongSixInternalIndex r)))
          (hpolygonSub (heMem 5))
        have hhead := hallowed.head_eq_of_third_ne_fourth hneq
        exact middleFailureBridgeCertificate_of_head hqfirst hfirstj hjlast
          hqInsert (insertMem (heMem 0))
          (insertMem (heMem (strongSixInternalIndex r)))
          (insertMem (heMem 5)) (Or.inl rfl) hhead.1 hhead.2
      · have hbridges := canonicalLeftAnomaly_inside_forces_reference_bridges
          hcard r hpolygonSub hqAmbient hone hfirstq ⟨hqj, hneq⟩
        exact middleFailureBridgeCertificate_of_head hfirstq hqj hjlast
          (insertMem (heMem 0)) hqInsert
          (insertMem (heMem (strongSixInternalIndex r)))
          (insertMem (heMem 5)) (Or.inr (Or.inl rfl))
          (hbridges.1.trans hbridges.2.symm) hbridges.2
  | firstFan =>
      change HasFirstMiddleFanVariation χ polygon hcard q at hclass
      obtain ⟨k, k', hqfirst, hfirstk, hfirstk', hk, hk', hneq⟩ := hclass
      have hkk' : k ≠ k' := by
        intro heq
        subst k'
        exact hneq rfl
      rcases lt_or_gt_of_ne hkk' with hkk' | hk'k
      · have hallowed := hone hqfirst hfirstk hkk' hqAmbient
          (hpolygonSub (heMem 0)) (hpolygonSub hk) (hpolygonSub hk')
        have htail := hallowed.tail_eq_of_first_ne_second hneq
        exact middleFailureBridgeCertificate_of_tail hqfirst hfirstk hkk'
          hqInsert (insertMem (heMem 0)) (insertMem hk) (insertMem hk')
          (Or.inl rfl) htail.1 htail.2
      · have hallowed := hone hqfirst hfirstk' hk'k hqAmbient
          (hpolygonSub (heMem 0)) (hpolygonSub hk') (hpolygonSub hk)
        have htail := hallowed.tail_eq_of_first_ne_second hneq.symm
        exact middleFailureBridgeCertificate_of_tail hqfirst hfirstk' hk'k
          hqInsert (insertMem (heMem 0)) (insertMem hk') (insertMem hk)
          (Or.inl rfl) htail.1 htail.2
  | leftFan r =>
      change HasInternalLeftEndpointFanVariationAt χ polygon hcard q r at hclass
      obtain ⟨a, b, hqj, hab, hja, _hjb, ha, hb, hfirst, hsecond⟩ :=
        internalLeftFanVariation_forces_bridge_colors hcard r hpolygonSub
          hqAmbient hone hclass
      exact middleFailureBridgeCertificate_of_tail hqj hja hab hqInsert
        (insertMem (heMem (strongSixInternalIndex r))) (insertMem ha)
        (insertMem hb) (Or.inl rfl) hfirst.symm
        (hfirst.trans hsecond.symm)
  | freshMiddleFan =>
      change HasFreshMiddleFanVariation χ polygon q at hclass
      rcases freshMiddleFanVariation_has_oneSided_fan hclass with hearlier | hlater
      · obtain ⟨a, b, k, hab, haq, hbq, hqk, ha, hb, hk,
          hfirst, hsecond⟩ :=
          freshMiddleEarlierFan_forces_bridge_colors hpolygonSub hqAmbient
            hone hearlier
        exact middleFailureBridgeCertificate_of_head hab hbq hqk
          (insertMem ha) (insertMem hb) hqInsert (insertMem hk)
          (Or.inr (Or.inr (Or.inl rfl))) (hfirst.trans hsecond.symm)
          hsecond
      · obtain ⟨i, a, b, hiq, hqa, _hqb, hab, hi, ha, hb,
          hfirst, hsecond⟩ :=
          freshMiddleLaterFan_forces_bridge_colors hpolygonSub hqAmbient
            hone hlater
        exact middleFailureBridgeCertificate_of_tail hiq hqa hab
          (insertMem hi) hqInsert (insertMem ha) (insertMem hb)
          (Or.inr (Or.inl rfl)) hfirst.symm (hfirst.trans hsecond.symm)
  | rightAnomaly r =>
      change HasCanonicalRightEndpointAnomalyAt χ polygon hcard q r at hclass
      let j := e (strongSixInternalIndex r)
      obtain ⟨hjq, hneq⟩ := hclass
      have hfirstj : e 0 < j := e.strictMono (by
        change 0 < r.val + 1
        omega)
      have hjlast : j < e 5 := e.strictMono (by
        change r.val + 1 < 5
        omega)
      have hqLast : q ≠ e 5 := fun heq ↦ hqPolygon (heq ▸ heMem 5)
      rcases lt_or_gt_of_ne hqLast with hqlast | hlastq
      · have hbridges := canonicalRightAnomaly_inside_forces_reference_bridges
          hcard r hpolygonSub hqAmbient hone hqlast ⟨hjq, hneq⟩
        exact middleFailureBridgeCertificate_of_tail hfirstj hjq hqlast
          (insertMem (heMem 0))
          (insertMem (heMem (strongSixInternalIndex r))) hqInsert
          (insertMem (heMem 5)) (Or.inr (Or.inr (Or.inl rfl)))
          hbridges.1.symm (hbridges.1.trans hbridges.2.symm)
      · have hallowed := hone hfirstj hjlast hlastq
          (hpolygonSub (heMem 0))
          (hpolygonSub (heMem (strongSixInternalIndex r)))
          (hpolygonSub (heMem 5)) hqAmbient
        have htail := hallowed.tail_eq_of_first_ne_second hneq.symm
        exact middleFailureBridgeCertificate_of_tail hfirstj hjlast hlastq
          (insertMem (heMem 0))
          (insertMem (heMem (strongSixInternalIndex r)))
          (insertMem (heMem 5)) hqInsert (Or.inr (Or.inr (Or.inr rfl)))
          htail.1 htail.2
  | rightFan r =>
      change HasInternalRightEndpointFanVariationAt χ polygon hcard q r at hclass
      obtain ⟨a, b, hab, haj, hbj, hjq, ha, hb, hfirst, hsecond⟩ :=
        internalRightFanVariation_forces_bridge_colors hcard r hpolygonSub
          hqAmbient hone hclass
      exact middleFailureBridgeCertificate_of_head hab hbj hjq
        (insertMem ha) (insertMem hb)
        (insertMem (heMem (strongSixInternalIndex r))) hqInsert
        (Or.inr (Or.inr (Or.inr rfl))) (hfirst.trans hsecond.symm)
        hsecond
  | finalFan =>
      change HasFinalMiddleFanVariation χ polygon hcard q at hclass
      obtain ⟨i, i', hi, hi', hlastq, hiMem, hi'Mem, hneq⟩ := hclass
      have hii' : i ≠ i' := by
        intro heq
        subst i'
        exact hneq rfl
      rcases lt_or_gt_of_ne hii' with hii' | hi'i
      · have hallowed := hone hii' hi' hlastq (hpolygonSub hiMem)
          (hpolygonSub hi'Mem) (hpolygonSub (heMem 5)) hqAmbient
        have hhead := hallowed.head_eq_of_third_ne_fourth hneq
        exact middleFailureBridgeCertificate_of_head hii' hi' hlastq
          (insertMem hiMem) (insertMem hi'Mem) (insertMem (heMem 5))
          hqInsert (Or.inr (Or.inr (Or.inr rfl))) hhead.1 hhead.2
      · have hallowed := hone hi'i hi hlastq (hpolygonSub hi'Mem)
          (hpolygonSub hiMem) (hpolygonSub (heMem 5)) hqAmbient
        have hhead := hallowed.head_eq_of_third_ne_fourth hneq.symm
        exact middleFailureBridgeCertificate_of_head hi'i hi hlastq
          (insertMem hi'Mem) (insertMem hiMem) (insertMem (heMem 5))
          hqInsert (Or.inr (Or.inr (Or.inr rfl))) hhead.1 hhead.2

/-- Every directed failure in a properly crossing mutually obstructed pair
has a common bridge certificate. -/
theorem mutuallyMiddleObstructedPair_has_bridgeCertificates
    {n : ℕ} {χ : TripleColoring n}
    {left right first second : Finset (Fin n)}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hfirstSub : first ⊆ left ∪ right)
    (hsecondSub : second ⊆ left ∪ right)
    (hfirstLeft : ∃ z ∈ first, z ∈ left)
    (hfirstRight : ∃ z ∈ first, z ∈ right)
    (hsecondLeft : ∃ z ∈ second, z ∈ left)
    (hsecondRight : ∃ z ∈ second, z ∈ right)
    (hone : OneChangeOn χ (left ∪ right))
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second) :
    (∀ q ∈ second, HasMiddleFailureBridgeCertificate χ first q) ∧
    (∀ q ∈ first, HasMiddleFailureBridgeCertificate χ second q) := by
  have hclasses := mutuallyMiddleObstructedPair_has_finite_failure_classes
    horder hfirstSub hsecondSub hfirstLeft hfirstRight hsecondLeft
      hsecondRight hmutual
  constructor
  · intro q hqSecond
    obtain ⟨c, hc⟩ := hclasses.1 q hqSecond
    exact normalizedCutFailureClass_has_bridgeCertificate hmutual.2.1
      hfirstSub (hsecondSub hqSecond)
      (fun hqFirst ↦ Finset.disjoint_left.mp hmutual.1 hqFirst hqSecond)
      hone c hc
  · intro q hqFirst
    obtain ⟨c, hc⟩ := hclasses.2 q hqFirst
    exact normalizedCutFailureClass_has_bridgeCertificate hmutual.2.2.1
      hsecondSub (hfirstSub hqFirst)
      (fun hqSecond ↦ Finset.disjoint_left.mp hmutual.1 hqFirst hqSecond)
      hone c hc

/-- Deletion packing lands directly in a disjoint partner carrying twelve
common bridge certificates. This bridge transition does not require the
additional cap-five or cup-six exclusions used to bound the middle words. -/
theorem packedStrongSix_has_bridgeCertificate_partner
    {n : ℕ} {χ : TripleColoring n} {left right first : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hone : OneChangeOn χ (left ∪ right))
    (hfirstSub : first ⊆ left ∪ right) (hfirstCard : first.card = 6)
    (hfirstStrong : IsStrongPolygonSet χ first)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    ∃ (second : Finset (Fin n)) (_hsecondSub : second ⊆ left ∪ right)
        (_hmutual : MutuallyMiddleObstructedStrongSixPair χ first second),
      (∀ q ∈ second, HasMiddleFailureBridgeCertificate χ first q) ∧
      (∀ q ∈ first, HasMiddleFailureBridgeCertificate χ second q) := by
  obtain ⟨second, hsecondSub, hmutual, hsecondSplitRaw⟩ :=
    packedStrongSix_has_mutuallyObstructed_split_partner hdisjoint hfirstSub
      hfirstCard hfirstStrong hpacking hnoLeftStrong hnoRightStrong
      hnoStrongSeven
  have hfirstSplit : HasProperStrongSixCrossingSplit first left right := by
    simpa only [HasProperStrongSixCrossingSplit] using
      strongSix_has_proper_crossing_split hdisjoint hfirstSub hfirstCard
        hfirstStrong hnoLeftStrong hnoRightStrong
  have hsecondSplit : HasProperStrongSixCrossingSplit second left right := by
    simpa only [HasProperStrongSixCrossingSplit] using hsecondSplitRaw
  obtain ⟨hfirstLeft, hfirstRight⟩ :=
    properStrongSixCrossingSplit_has_side_vertices hfirstSplit
  obtain ⟨hsecondLeft, hsecondRight⟩ :=
    properStrongSixCrossingSplit_has_side_vertices hsecondSplit
  exact ⟨second, hsecondSub, hmutual,
    mutuallyMiddleObstructedPair_has_bridgeCertificates horder hfirstSub
      hsecondSub hfirstLeft hfirstRight hsecondLeft hsecondRight hone hmutual⟩

end ErdosSzekeres

end
