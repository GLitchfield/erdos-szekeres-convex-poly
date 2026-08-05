module

public import ErdosSzekeres.StructuralChargingMiddleSplits

@[expose] public section

/-!
# Finite classes for middle crossing failures

This file indexes every internal-middle anomaly and fan variation from the
crossing strong-six state. The resulting literal finite type is the input to
the next compatibility and counting arguments.
-/

namespace ErdosSzekeres

/-- A left-endpoint anomaly at one specified internal strong-six position. -/
def HasInternalLeftEndpointAnomalyAt {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n)
    (r : Fin 4) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  ∃ (k : Fin n) (hqj : q < j) (hjk : j < k),
    k ∈ polygon ∧
      χ ⟨q, j, k, hqj, hjk⟩ ≠
        χ ⟨e 0, j, e 5, e.strictMono (by
            change 0 < r.val + 1
            omega), e.strictMono (by
            change r.val + 1 < 5
            omega)⟩

/-- A left-endpoint fan variation at one specified internal position. -/
def HasInternalLeftEndpointFanVariationAt {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n)
    (r : Fin 4) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  ∃ (k k' : Fin n) (hqj : q < j) (hjk : j < k) (hjk' : j < k'),
    k ∈ polygon ∧ k' ∈ polygon ∧
      χ ⟨q, j, k, hqj, hjk⟩ ≠ χ ⟨q, j, k', hqj, hjk'⟩

/-- A right-endpoint fan variation at one specified internal position. -/
def HasInternalRightEndpointFanVariationAt {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n)
    (r : Fin 4) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  ∃ (i i' : Fin n) (hij : i < j) (hi'j : i' < j) (hjq : j < q),
    i ∈ polygon ∧ i' ∈ polygon ∧
      χ ⟨i, j, q, hij, hjq⟩ ≠ χ ⟨i', j, q, hi'j, hjq⟩

/-- A fresh-middle fan variation obtained by changing only the earlier
polygon endpoint. -/
def HasFreshMiddleEarlierFanVariation {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ (i i' k : Fin n) (hiq : i < q) (hi'q : i' < q) (hqk : q < k),
    i ∈ polygon ∧ i' ∈ polygon ∧ k ∈ polygon ∧
      χ ⟨i, q, k, hiq, hqk⟩ ≠ χ ⟨i', q, k, hi'q, hqk⟩

/-- A fresh-middle fan variation obtained by changing only the later polygon
endpoint. -/
def HasFreshMiddleLaterFanVariation {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ (i k k' : Fin n) (hiq : i < q) (hqk : q < k) (hqk' : q < k'),
    i ∈ polygon ∧ k ∈ polygon ∧ k' ∈ polygon ∧
      χ ⟨i, q, k, hiq, hqk⟩ ≠ χ ⟨i, q, k', hiq, hqk'⟩

/-- Every fresh-middle fan variation contains a one-sided fan variation. -/
theorem freshMiddleFanVariation_has_oneSided_fan
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hfan : HasFreshMiddleFanVariation χ polygon q) :
    HasFreshMiddleEarlierFanVariation χ polygon q ∨
      HasFreshMiddleLaterFanVariation χ polygon q := by
  obtain ⟨i, i', k, k', hiq, hi'q, hqk, hqk', hi, hi', hk, hk', hneq⟩ := hfan
  by_cases hearlier :
      χ ⟨i, q, k, hiq, hqk⟩ ≠ χ ⟨i', q, k, hi'q, hqk⟩
  · exact Or.inl ⟨i, i', k, hiq, hi'q, hqk, hi, hi', hk, hearlier⟩
  · have heq := not_ne_iff.mp hearlier
    exact Or.inr ⟨i', k, k', hi'q, hqk, hqk', hi', hk, hk', by
      intro hlaterEq
      exact hneq (heq.trans hlaterEq)⟩

/-- Every polygon vertex strictly between the endpoints of a strong six has
one of the four canonical internal indices. -/
theorem strongSix_internal_vertex_has_index
    {n : ℕ} {polygon : Finset (Fin n)} {j : Fin n}
    (hcard : polygon.card = 6) (hj : j ∈ polygon)
    (hfirst : polygon.orderEmbOfFin hcard 0 < j)
    (hlast : j < polygon.orderEmbOfFin hcard 5) :
    ∃ r : Fin 4, polygon.orderEmbOfFin hcard (strongSixInternalIndex r) = j := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heImage : Finset.univ.image e = polygon :=
    Finset.image_orderEmbOfFin_univ polygon hcard
  have hjImage : j ∈ Finset.univ.image e := by simpa [heImage] using hj
  obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hjImage
  subst j
  fin_cases s
  · exact (lt_irrefl _ hfirst).elim
  · exact ⟨0, by simp [e, strongSixInternalIndex]⟩
  · exact ⟨1, by simp [e, strongSixInternalIndex]⟩
  · exact ⟨2, by simp [e, strongSixInternalIndex]⟩
  · exact ⟨3, by simp [e, strongSixInternalIndex]⟩
  · exact (lt_irrefl _ hlast).elim

/-- Every internal left-endpoint anomaly has an explicit position. -/
theorem internalLeftEndpointMiddleAnomaly_has_index
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hcard : polygon.card = 6)
    (hanomaly : HasInternalLeftEndpointMiddleAnomaly χ polygon hcard q) :
    ∃ r : Fin 4, HasInternalLeftEndpointAnomalyAt χ polygon hcard q r := by
  obtain ⟨j, k, hqj, hjk, hfirst, hlast, hj, hk, hneq⟩ := hanomaly
  obtain ⟨r, hr⟩ :=
    strongSix_internal_vertex_has_index hcard hj hfirst hlast
  subst j
  exact ⟨r, k, hqj, hjk, hk, hneq⟩

/-- Every internal left fan variation has an explicit position. -/
theorem internalLeftEndpointFanVariation_has_index
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hcard : polygon.card = 6)
    (hfan : HasInternalLeftEndpointFanVariation χ polygon hcard q) :
    ∃ r : Fin 4, HasInternalLeftEndpointFanVariationAt χ polygon hcard q r := by
  obtain ⟨j, k, k', hqj, hjk, hjk', hfirst, hlast, _hj, hk, hk', hneq⟩ := hfan
  obtain ⟨r, hr⟩ :=
    strongSix_internal_vertex_has_index hcard _hj hfirst hlast
  subst j
  exact ⟨r, k, k', hqj, hjk, hjk', hk, hk', hneq⟩

/-- Every internal right fan variation has an explicit position. -/
theorem internalRightEndpointFanVariation_has_index
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hcard : polygon.card = 6)
    (hfan : HasInternalRightEndpointFanVariation χ polygon hcard q) :
    ∃ r : Fin 4, HasInternalRightEndpointFanVariationAt χ polygon hcard q r := by
  obtain ⟨i, i', j, hij, hi'j, hjq, hfirst, hlast, hi, hi', hj, hneq⟩ := hfan
  obtain ⟨r, hr⟩ :=
    strongSix_internal_vertex_has_index hcard hj hfirst hlast
  subst j
  exact ⟨r, i, i', hij, hi'j, hjq, hi, hi', hneq⟩

/-- A left-endpoint anomaly normalized to the final polygon endpoint. -/
def HasCanonicalLeftEndpointAnomalyAt {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n)
    (r : Fin 4) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  ∃ (hqj : q < j),
    χ ⟨q, j, e 5, hqj, e.strictMono (by
        change r.val + 1 < 5
        omega)⟩ ≠
      χ ⟨e 0, j, e 5, e.strictMono (by
          change 0 < r.val + 1
          omega), e.strictMono (by
          change r.val + 1 < 5
          omega)⟩

/-- A right-endpoint anomaly normalized to the first polygon endpoint. -/
def HasCanonicalRightEndpointAnomalyAt {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n)
    (r : Fin 4) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  ∃ (hjq : j < q),
    χ ⟨e 0, j, q, e.strictMono (by
        change 0 < r.val + 1
        omega), hjq⟩ ≠
      χ ⟨e 0, j, e 5, e.strictMono (by
          change 0 < r.val + 1
          omega), e.strictMono (by
          change r.val + 1 < 5
          omega)⟩

/-- An arbitrary left anomaly either reaches the canonical final endpoint or
exhibits a fan variation at the same internal position. -/
theorem internalLeftEndpointAnomalyAt_canonical_or_fan
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hcard : polygon.card = 6) (r : Fin 4)
    (hanomaly : HasInternalLeftEndpointAnomalyAt χ polygon hcard q r) :
    HasCanonicalLeftEndpointAnomalyAt χ polygon hcard q r ∨
      HasInternalLeftEndpointFanVariationAt χ polygon hcard q r := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  obtain ⟨k, hqj, hjk, hk, hneq⟩ := hanomaly
  have hjlast : j < e 5 := e.strictMono (by
    change r.val + 1 < 5
    omega)
  have hlastMem : e 5 ∈ polygon := polygon.orderEmbOfFin_mem hcard 5
  by_cases hcanonical :
      χ ⟨q, j, e 5, hqj, hjlast⟩ ≠
        χ ⟨e 0, j, e 5, e.strictMono (by
            change 0 < r.val + 1
            omega), hjlast⟩
  · exact Or.inl ⟨hqj, hcanonical⟩
  · have heq := not_ne_iff.mp hcanonical
    exact Or.inr ⟨k, e 5, hqj, hjk, hjlast, hk, hlastMem, by
      intro hfanEq
      exact hneq (hfanEq.trans heq)⟩

/-- An arbitrary right anomaly either reaches the canonical first endpoint or
exhibits a fan variation at the same internal position. -/
theorem internalRightEndpointAnomalyAt_canonical_or_fan
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hcard : polygon.card = 6) (r : Fin 4)
    (hanomaly : HasInternalRightEndpointAnomalyAt χ polygon hcard q r) :
    HasCanonicalRightEndpointAnomalyAt χ polygon hcard q r ∨
      HasInternalRightEndpointFanVariationAt χ polygon hcard q r := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  obtain ⟨i, hij, hjq, hi, hneq⟩ := hanomaly
  have hfirstj : e 0 < j := e.strictMono (by
    change 0 < r.val + 1
    omega)
  have hfirstMem : e 0 ∈ polygon := polygon.orderEmbOfFin_mem hcard 0
  by_cases hcanonical :
      χ ⟨e 0, j, q, hfirstj, hjq⟩ ≠
        χ ⟨e 0, j, e 5, hfirstj, e.strictMono (by
            change r.val + 1 < 5
            omega)⟩
  · exact Or.inl ⟨hjq, hcanonical⟩
  · have heq := not_ne_iff.mp hcanonical
    exact Or.inr ⟨i, e 0, hij, hfirstj, hjq, hi, hfirstMem, by
      intro hfanEq
      exact hneq (hfanEq.trans heq)⟩

/-- An interleaving canonical left anomaly forces both earlier bridge colors
to equal the polygon's reference color at the indexed middle. -/
theorem canonicalLeftAnomaly_inside_forces_reference_bridges
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hcard : polygon.card = 6) (r : Fin 4)
    (hpolygonSub : polygon ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hfirstq : polygon.orderEmbOfFin hcard 0 < q)
    (hanomaly : HasCanonicalLeftEndpointAnomalyAt χ polygon hcard q r) :
    let e := polygon.orderEmbOfFin hcard
    let j := e (strongSixInternalIndex r)
    χ ⟨e 0, q, j, hfirstq, hanomaly.choose⟩ =
        χ ⟨e 0, j, e 5, e.strictMono (by
          change 0 < r.val + 1
          omega), e.strictMono (by
          change r.val + 1 < 5
          omega)⟩ ∧
      χ ⟨e 0, q, e 5, hfirstq,
          hanomaly.choose.trans (e.strictMono (by
            change r.val + 1 < 5
            omega))⟩ =
        χ ⟨e 0, j, e 5, e.strictMono (by
          change 0 < r.val + 1
          omega), e.strictMono (by
          change r.val + 1 < 5
          omega)⟩ := by
  dsimp only
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  obtain ⟨hqj, hneq⟩ := hanomaly
  have hjlast : j < e 5 := e.strictMono (by
    change r.val + 1 < 5
    omega)
  have heMem (s : Fin 6) : e s ∈ polygon := polygon.orderEmbOfFin_mem hcard s
  have hallowed := hone hfirstq hqj hjlast (hpolygonSub (heMem 0))
    hqAmbient (hpolygonSub (heMem (strongSixInternalIndex r)))
    (hpolygonSub (heMem 5))
  have hhead := hallowed.head_eq_of_third_ne_fourth hneq.symm
  exact ⟨hhead.1.trans hhead.2, hhead.2⟩

/-- An interleaving canonical right anomaly forces both later bridge colors
to equal the polygon's reference color at the indexed middle. -/
theorem canonicalRightAnomaly_inside_forces_reference_bridges
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hcard : polygon.card = 6) (r : Fin 4)
    (hpolygonSub : polygon ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hqlast : q < polygon.orderEmbOfFin hcard 5)
    (hanomaly : HasCanonicalRightEndpointAnomalyAt χ polygon hcard q r) :
    let e := polygon.orderEmbOfFin hcard
    let j := e (strongSixInternalIndex r)
    χ ⟨e 0, q, e 5, (e.strictMono (by
          change 0 < r.val + 1
          omega)).trans hanomaly.choose, hqlast⟩ =
        χ ⟨e 0, j, e 5, e.strictMono (by
          change 0 < r.val + 1
          omega), e.strictMono (by
          change r.val + 1 < 5
          omega)⟩ ∧
      χ ⟨j, q, e 5, hanomaly.choose, hqlast⟩ =
        χ ⟨e 0, j, e 5, e.strictMono (by
          change 0 < r.val + 1
          omega), e.strictMono (by
          change r.val + 1 < 5
          omega)⟩ := by
  dsimp only
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  obtain ⟨hjq, hneq⟩ := hanomaly
  have hfirstj : e 0 < j := e.strictMono (by
    change 0 < r.val + 1
    omega)
  have heMem (s : Fin 6) : e s ∈ polygon := polygon.orderEmbOfFin_mem hcard s
  have hallowed := hone hfirstj hjq hqlast (hpolygonSub (heMem 0))
    (hpolygonSub (heMem (strongSixInternalIndex r))) hqAmbient
    (hpolygonSub (heMem 5))
  have htail := hallowed.tail_eq_of_first_ne_second hneq
  exact ⟨htail.1.symm, htail.2.symm.trans htail.1.symm⟩

/-- A change in the first-middle fan forces the later fan color and its bridge
to equal the strong polygon's reference color at the earlier later endpoint.
This is the order-dual of `finalMiddleFan_variation_forces_later_middle_color`. -/
theorem firstMiddleFan_variation_forces_earlier_middle_color
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hcard : polygon.card = 6)
    (hpolygonSub : polygon ⊆ ambient)
    (hstrong : IsStrongPolygonSet χ polygon)
    (hqAmbient : q ∈ ambient)
    (hbefore : q < polygon.orderEmbOfFin hcard 0)
    (hone : OneChangeOn χ ambient)
    {a b : Fin 6} (h0a : (0 : Fin 6) < a) (hab : a < b)
    (hvariation :
      χ ⟨q, polygon.orderEmbOfFin hcard 0, polygon.orderEmbOfFin hcard a,
        hbefore, (polygon.orderEmbOfFin hcard).strictMono h0a⟩ ≠
      χ ⟨q, polygon.orderEmbOfFin hcard 0, polygon.orderEmbOfFin hcard b,
        hbefore, (polygon.orderEmbOfFin hcard).strictMono (h0a.trans hab)⟩) :
    let e := polygon.orderEmbOfFin hcard
    χ ⟨q, e 0, e b, hbefore, e.strictMono (h0a.trans hab)⟩ =
        χ ⟨e 0, e a, e 5, e.strictMono h0a,
          e.strictMono (hab.trans_le (Fin.le_last b))⟩ ∧
      χ ⟨q, e a, e b, hbefore.trans (e.strictMono h0a), e.strictMono hab⟩ =
        χ ⟨e 0, e a, e 5, e.strictMono h0a,
          e.strictMono (hab.trans_le (Fin.le_last b))⟩ := by
  dsimp only
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (s : Fin 6) : e s ∈ polygon := polygon.orderEmbOfFin_mem hcard s
  have hallowed := hone hbefore (e.strictMono h0a) (e.strictMono hab)
    hqAmbient (hpolygonSub (heMem 0)) (hpolygonSub (heMem a))
    (hpolygonSub (heMem b))
  have htail := hallowed.tail_eq_of_first_ne_second (by
    simpa [e] using hvariation)
  have hmiddle : IsMiddleDeterminedOn χ polygon :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
  have ha5 : a < (5 : Fin 6) := hab.trans_le (Fin.le_last b)
  have hreference :
      χ ⟨e 0, e a, e b, e.strictMono h0a, e.strictMono hab⟩ =
        χ ⟨e 0, e a, e 5, e.strictMono h0a, e.strictMono ha5⟩ :=
    hmiddle (e.strictMono h0a) (e.strictMono h0a)
      (e.strictMono hab) (e.strictMono ha5)
      (heMem 0) (heMem 0) (heMem a) (heMem b) (heMem 5)
  exact ⟨htail.1.trans (htail.2.trans hreference), htail.2.trans hreference⟩

/-- An internal left fan variation can be ordered so that the two bridge
triples through its later endpoint take the later fan color. -/
theorem internalLeftFanVariation_forces_bridge_colors
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hcard : polygon.card = 6) (r : Fin 4)
    (hpolygonSub : polygon ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hfan : HasInternalLeftEndpointFanVariationAt χ polygon hcard q r) :
    let e := polygon.orderEmbOfFin hcard
    let j := e (strongSixInternalIndex r)
    ∃ (a b : Fin n) (hqj : q < j) (hab : a < b) (hja : j < a) (hjb : j < b),
      a ∈ polygon ∧ b ∈ polygon ∧
      χ ⟨q, a, b, hqj.trans hja, hab⟩ =
          χ ⟨q, j, b, hqj, hjb⟩ ∧
        χ ⟨j, a, b, hja, hab⟩ =
          χ ⟨q, j, b, hqj, hjb⟩ := by
  dsimp only
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  obtain ⟨k, k', hqj, hjk, hjk', hk, hk', hneq⟩ := hfan
  have hjMem : j ∈ polygon :=
    polygon.orderEmbOfFin_mem hcard (strongSixInternalIndex r)
  have hkk' : k ≠ k' := by
    intro heq
    subst k'
    exact hneq rfl
  rcases lt_or_gt_of_ne hkk' with hkk' | hk'k
  · have htransition := hone.probe_transition_forces_pair_colors hqj hjk
      hkk' hqAmbient (hpolygonSub hjMem) (hpolygonSub hk)
      (hpolygonSub hk') hneq
    exact ⟨k, k', hqj, hkk', hjk, hjk', hk, hk', htransition⟩
  · have htransition := hone.probe_transition_forces_pair_colors hqj hjk'
      hk'k hqAmbient (hpolygonSub hjMem) (hpolygonSub hk')
      (hpolygonSub hk) hneq.symm
    exact ⟨k', k, hqj, hk'k, hjk', hjk, hk', hk, htransition⟩

/-- Order-dually, an internal right fan variation forces the two bridge
triples through its earlier endpoint to take the earlier fan color. -/
theorem internalRightFanVariation_forces_bridge_colors
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hcard : polygon.card = 6) (r : Fin 4)
    (hpolygonSub : polygon ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hfan : HasInternalRightEndpointFanVariationAt χ polygon hcard q r) :
    let e := polygon.orderEmbOfFin hcard
    let j := e (strongSixInternalIndex r)
    ∃ (a b : Fin n) (hab : a < b) (haj : a < j) (hbj : b < j) (hjq : j < q),
      a ∈ polygon ∧ b ∈ polygon ∧
      χ ⟨a, b, j, hab, hbj⟩ = χ ⟨a, j, q, haj, hjq⟩ ∧
        χ ⟨a, b, q, hab, hbj.trans hjq⟩ =
          χ ⟨a, j, q, haj, hjq⟩ := by
  dsimp only
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  let j := e (strongSixInternalIndex r)
  obtain ⟨i, i', hij, hi'j, hjq, hi, hi', hneq⟩ := hfan
  have hjMem : j ∈ polygon :=
    polygon.orderEmbOfFin_mem hcard (strongSixInternalIndex r)
  have hii' : i ≠ i' := by
    intro heq
    subst i'
    exact hneq rfl
  rcases lt_or_gt_of_ne hii' with hii' | hi'i
  · have hallowed := hone hii' hi'j hjq (hpolygonSub hi)
      (hpolygonSub hi') (hpolygonSub hjMem) hqAmbient
    have hhead := hallowed.head_eq_of_third_ne_fourth hneq
    exact ⟨i, i', hii', hij, hi'j, hjq, hi, hi', hhead.1.trans hhead.2, hhead.2⟩
  · have hallowed := hone hi'i hij hjq (hpolygonSub hi')
      (hpolygonSub hi) (hpolygonSub hjMem) hqAmbient
    have hhead := hallowed.head_eq_of_third_ne_fourth hneq.symm
    exact ⟨i', i, hi'i, hi'j, hij, hjq, hi', hi, hhead.1.trans hhead.2, hhead.2⟩

/-- The earlier-endpoint branch of a fresh-middle fan forces its two head
bridge triples to take the earlier fan color. -/
theorem freshMiddleEarlierFan_forces_bridge_colors
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hpolygonSub : polygon ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hfan : HasFreshMiddleEarlierFanVariation χ polygon q) :
    ∃ (a b k : Fin n) (hab : a < b) (haq : a < q) (hbq : b < q) (hqk : q < k),
      a ∈ polygon ∧ b ∈ polygon ∧ k ∈ polygon ∧
      χ ⟨a, b, q, hab, hbq⟩ = χ ⟨a, q, k, haq, hqk⟩ ∧
        χ ⟨a, b, k, hab, hbq.trans hqk⟩ =
          χ ⟨a, q, k, haq, hqk⟩ := by
  obtain ⟨i, i', k, hiq, hi'q, hqk, hi, hi', hk, hneq⟩ := hfan
  have hii' : i ≠ i' := by
    intro heq
    subst i'
    exact hneq rfl
  rcases lt_or_gt_of_ne hii' with hii' | hi'i
  · have hallowed := hone hii' hi'q hqk (hpolygonSub hi)
      (hpolygonSub hi') hqAmbient (hpolygonSub hk)
    have hhead := hallowed.head_eq_of_third_ne_fourth hneq
    exact ⟨i, i', k, hii', hiq, hi'q, hqk, hi, hi', hk,
      hhead.1.trans hhead.2, hhead.2⟩
  · have hallowed := hone hi'i hiq hqk (hpolygonSub hi')
      (hpolygonSub hi) hqAmbient (hpolygonSub hk)
    have hhead := hallowed.head_eq_of_third_ne_fourth hneq.symm
    exact ⟨i', i, k, hi'i, hi'q, hiq, hqk, hi', hi, hk,
      hhead.1.trans hhead.2, hhead.2⟩

/-- The later-endpoint branch of a fresh-middle fan forces its two tail
bridge triples to take the later fan color. -/
theorem freshMiddleLaterFan_forces_bridge_colors
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hpolygonSub : polygon ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hfan : HasFreshMiddleLaterFanVariation χ polygon q) :
    ∃ (i a b : Fin n) (hiq : i < q) (hqa : q < a) (hqb : q < b) (hab : a < b),
      i ∈ polygon ∧ a ∈ polygon ∧ b ∈ polygon ∧
      χ ⟨i, a, b, hiq.trans hqa, hab⟩ = χ ⟨i, q, b, hiq, hqb⟩ ∧
        χ ⟨q, a, b, hqa, hab⟩ = χ ⟨i, q, b, hiq, hqb⟩ := by
  obtain ⟨i, k, k', hiq, hqk, hqk', hi, hk, hk', hneq⟩ := hfan
  have hkk' : k ≠ k' := by
    intro heq
    subst k'
    exact hneq rfl
  rcases lt_or_gt_of_ne hkk' with hkk' | hk'k
  · have htransition := hone.probe_transition_forces_pair_colors hiq hqk
      hkk' (hpolygonSub hi) hqAmbient (hpolygonSub hk) (hpolygonSub hk')
      hneq
    exact ⟨i, k, k', hiq, hqk, hqk', hkk', hi, hk, hk', htransition⟩
  · have htransition := hone.probe_transition_forces_pair_colors hiq hqk'
      hk'k (hpolygonSub hi) hqAmbient (hpolygonSub hk') (hpolygonSub hk)
      hneq.symm
    exact ⟨i, k', k, hiq, hqk', hqk, hk'k, hi, hk', hk, htransition⟩

/-- The nineteen nominal normalized failure classes. A vertex on either fixed
side can realize only eighteen of them. -/
inductive NormalizedCutFailureClass where
  | leftAnomaly (r : Fin 4)
  | firstFan
  | leftFan (r : Fin 4)
  | freshMiddleFan
  | rightAnomaly (r : Fin 4)
  | rightFan (r : Fin 4)
  | finalFan
  deriving DecidableEq, Fintype

theorem normalizedCutFailureClass_card :
    Fintype.card NormalizedCutFailureClass = 19 := by
  decide

/-- Interpretation of a nominal class relative to a particular strong six
and probe vertex. -/
def RealizesNormalizedCutFailureClass {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n) :
    NormalizedCutFailureClass → Prop
  | .leftAnomaly r => HasCanonicalLeftEndpointAnomalyAt χ polygon hcard q r
  | .firstFan => HasFirstMiddleFanVariation χ polygon hcard q
  | .leftFan r => HasInternalLeftEndpointFanVariationAt χ polygon hcard q r
  | .freshMiddleFan => HasFreshMiddleFanVariation χ polygon q
  | .rightAnomaly r => HasCanonicalRightEndpointAnomalyAt χ polygon hcard q r
  | .rightFan r => HasInternalRightEndpointFanVariationAt χ polygon hcard q r
  | .finalFan => HasFinalMiddleFanVariation χ polygon hcard q

/-- Every fully normalized failure realizes at least one literal finite class. -/
theorem fullyNormalizedCutFailure_has_finite_class
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)} {q : Fin n}
    (hcard : polygon.card = 6)
    (hqSide : q ∈ left ∨ q ∈ right)
    (hfailure : HasFullyNormalizedCutFailure χ left right polygon hcard q) :
    ∃ c : NormalizedCutFailureClass,
      RealizesNormalizedCutFailureClass χ polygon hcard q c := by
  rcases hqSide with hqLeft | hqRight
  · rcases hfailure.1 hqLeft with hanomaly | hfirst | hfresh | hanomaly | hfan
    · obtain ⟨r, hr⟩ := internalLeftEndpointMiddleAnomaly_has_index hcard hanomaly
      rcases internalLeftEndpointAnomalyAt_canonical_or_fan hcard r hr with
          hcanonical | hfan
      · exact ⟨.leftAnomaly r, hcanonical⟩
      · exact ⟨.leftFan r, hfan⟩
    · exact ⟨.firstFan, hfirst⟩
    · exact ⟨.freshMiddleFan, hfresh⟩
    · obtain ⟨r, hr⟩ := internalRightEndpointMiddleAnomaly_has_index hcard hanomaly
      rcases internalRightEndpointAnomalyAt_canonical_or_fan hcard r hr with
          hcanonical | hfan
      · exact ⟨.rightAnomaly r, hcanonical⟩
      · exact ⟨.rightFan r, hfan⟩
    · obtain ⟨r, hr⟩ := internalRightEndpointFanVariation_has_index hcard hfan
      exact ⟨.rightFan r, hr⟩
  · rcases hfailure.2 hqRight with hanomaly | hfan | hfresh | hanomaly | hfinal
    · obtain ⟨r, hr⟩ := internalLeftEndpointMiddleAnomaly_has_index hcard hanomaly
      rcases internalLeftEndpointAnomalyAt_canonical_or_fan hcard r hr with
          hcanonical | hfan
      · exact ⟨.leftAnomaly r, hcanonical⟩
      · exact ⟨.leftFan r, hfan⟩
    · obtain ⟨r, hr⟩ := internalLeftEndpointFanVariation_has_index hcard hfan
      exact ⟨.leftFan r, hr⟩
    · exact ⟨.freshMiddleFan, hfresh⟩
    · obtain ⟨r, hr⟩ := internalRightEndpointMiddleAnomaly_has_index hcard hanomaly
      rcases internalRightEndpointAnomalyAt_canonical_or_fan hcard r hr with
          hcanonical | hfan
      · exact ⟨.rightAnomaly r, hcanonical⟩
      · exact ⟨.rightFan r, hfan⟩
    · exact ⟨.finalFan, hfinal⟩

/-- Finite-codomain form of all twelve directed failures in a properly
crossing mutually obstructed pair. -/
theorem mutuallyMiddleObstructedPair_has_finite_failure_classes
    {n : ℕ} {χ : TripleColoring n}
    {left right first second : Finset (Fin n)}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hfirstSub : first ⊆ left ∪ right)
    (hsecondSub : second ⊆ left ∪ right)
    (hfirstLeft : ∃ z ∈ first, z ∈ left)
    (hfirstRight : ∃ z ∈ first, z ∈ right)
    (hsecondLeft : ∃ z ∈ second, z ∈ left)
    (hsecondRight : ∃ z ∈ second, z ∈ right)
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second) :
    (∀ q ∈ second, ∃ c : NormalizedCutFailureClass,
      RealizesNormalizedCutFailureClass χ first hmutual.2.1 q c) ∧
    (∀ q ∈ first, ∃ c : NormalizedCutFailureClass,
      RealizesNormalizedCutFailureClass χ second hmutual.2.2.1 q c) := by
  have hnormalized :=
    mutuallyMiddleObstructedPair_has_fullyNormalized_failures horder
      hfirstSub hsecondSub hfirstLeft hfirstRight hsecondLeft hsecondRight
      hmutual
  constructor
  · intro q hqSecond
    exact fullyNormalizedCutFailure_has_finite_class hmutual.2.1
      (Finset.mem_union.mp (hsecondSub hqSecond)) (hnormalized.1 q hqSecond)
  · intro q hqFirst
    exact fullyNormalizedCutFailure_has_finite_class hmutual.2.2.1
      (Finset.mem_union.mp (hfirstSub hqFirst)) (hnormalized.2 q hqFirst)

end ErdosSzekeres

end
