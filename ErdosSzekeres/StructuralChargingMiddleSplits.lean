module

public import ErdosSzekeres.StructuralChargingPackingResidues

@[expose] public section

/-!
# Middle crossing strong-six states

This file records the local middle-color signature of a strong six under the
ambient `(5,6)` exclusions and the honest packing transition obtained by
deleting one middle-split witness.
-/

namespace ErdosSzekeres

/-- Three right-colored internal middle positions of a strong six form a cap
five through the two endpoints. -/
theorem strongSix_three_right_middles_force_capFive
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (a b c : Fin 6) (ha0 : (0 : Fin 6) < a) (hab : a < b)
    (hbc : b < c) (hc5 : c < (5 : Fin 6))
    (ha : χ ⟨polygon.orderEmbOfFin hcard 0,
        polygon.orderEmbOfFin hcard a, polygon.orderEmbOfFin hcard 5,
        (polygon.orderEmbOfFin hcard).strictMono ha0,
        (polygon.orderEmbOfFin hcard).strictMono (hab.trans (hbc.trans hc5))⟩ =
      Turn.right)
    (hb : χ ⟨polygon.orderEmbOfFin hcard 0,
        polygon.orderEmbOfFin hcard b, polygon.orderEmbOfFin hcard 5,
        (polygon.orderEmbOfFin hcard).strictMono (ha0.trans hab),
        (polygon.orderEmbOfFin hcard).strictMono (hbc.trans hc5)⟩ = Turn.right)
    (hc : χ ⟨polygon.orderEmbOfFin hcard 0,
        polygon.orderEmbOfFin hcard c, polygon.orderEmbOfFin hcard 5,
        (polygon.orderEmbOfFin hcard).strictMono (ha0.trans (hab.trans hbc)),
        (polygon.orderEmbOfFin hcard).strictMono hc5⟩ = Turn.right) :
    ContainsCapSet χ polygon 5 := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (i : Fin 6) : e i ∈ polygon := polygon.orderEmbOfFin_mem hcard i
  have hmiddle : IsMiddleDeterminedOn χ polygon :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
  let g : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![e 0, e a, e b, e c, e 5] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact e.strictMono ha0
        | exact e.strictMono (ha0.trans hab)
        | exact e.strictMono (ha0.trans (hab.trans hbc))
        | exact e.strictMono (ha0.trans (hab.trans (hbc.trans hc5)))
        | exact e.strictMono hab
        | exact e.strictMono (hab.trans hbc)
        | exact e.strictMono (hab.trans (hbc.trans hc5))
        | exact e.strictMono hbc
        | exact e.strictMono (hbc.trans hc5)
        | exact e.strictMono hc5)
  have hgMem (i : Fin 5) : g i ∈ polygon := by
    fin_cases i <;> simp [g, heMem]
  have hgSub : Finset.univ.image g ⊆ polygon := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hgMem i
  refine ⟨Finset.univ.image g, hgSub,
    by simpa using Finset.card_image_of_injective Finset.univ g.injective,
    FinsetPolygon.IsCap.image ?_⟩
  refine ⟨g.strictMono, ?_⟩
  intro i j k hij hjk
  fin_cases j
  · change i.val < 0 at hij
    omega
  · have heq := hmiddle (g.strictMono hij) (e.strictMono ha0)
      (g.strictMono hjk) (e.strictMono (hab.trans (hbc.trans hc5)))
      (hgMem i) (heMem 0) (hgMem 1) (hgMem k) (heMem 5)
    simpa [g, e] using heq.trans ha
  · have heq := hmiddle (g.strictMono hij) (e.strictMono (ha0.trans hab))
      (g.strictMono hjk) (e.strictMono (hbc.trans hc5))
      (hgMem i) (heMem 0) (hgMem 2) (hgMem k) (heMem 5)
    simpa [g, e] using heq.trans hb
  · have heq := hmiddle (g.strictMono hij)
      (e.strictMono (ha0.trans (hab.trans hbc)))
      (g.strictMono hjk) (e.strictMono hc5)
      (hgMem i) (heMem 0) (hgMem 3) (hgMem k) (heMem 5)
    simpa [g, e] using heq.trans hc
  · change 4 < k.val at hjk
    omega

/-- If all four internal middle positions of a strong six are left, the whole
six-set is a cup. -/
theorem strongSix_all_left_middles_force_cupSix
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (h1 : χ ⟨polygon.orderEmbOfFin hcard 0,
        polygon.orderEmbOfFin hcard 1, polygon.orderEmbOfFin hcard 5,
        by simp, by simp⟩ = Turn.left)
    (h2 : χ ⟨polygon.orderEmbOfFin hcard 0,
        polygon.orderEmbOfFin hcard 2, polygon.orderEmbOfFin hcard 5,
        by simp, by simp⟩ = Turn.left)
    (h3 : χ ⟨polygon.orderEmbOfFin hcard 0,
        polygon.orderEmbOfFin hcard 3, polygon.orderEmbOfFin hcard 5,
        by simp, by simp⟩ = Turn.left)
    (h4 : χ ⟨polygon.orderEmbOfFin hcard 0,
        polygon.orderEmbOfFin hcard 4, polygon.orderEmbOfFin hcard 5,
        by simp, by simp⟩ = Turn.left) :
    ContainsCupSet χ polygon 6 := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (i : Fin 6) : e i ∈ polygon := polygon.orderEmbOfFin_mem hcard i
  have heImage : Finset.univ.image e = polygon :=
    Finset.image_orderEmbOfFin_univ polygon hcard
  have hmiddle : IsMiddleDeterminedOn χ polygon :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
  have hcolor (i j k : Fin 6) (hij : i < j) (hjk : j < k)
      (hj0 : (0 : Fin 6) < j) (hj5 : j < (5 : Fin 6)) :
      χ ⟨e i, e j, e k, e.strictMono hij, e.strictMono hjk⟩ =
        χ ⟨e 0, e j, e 5, e.strictMono hj0, e.strictMono hj5⟩ :=
    hmiddle (e.strictMono hij) (e.strictMono hj0)
      (e.strictMono hjk) (e.strictMono hj5)
      (heMem i) (heMem 0) (heMem j) (heMem k) (heMem 5)
  refine ⟨polygon, Finset.Subset.rfl, hcard, ?_⟩
  rw [← heImage]
  apply FinsetPolygon.IsCup.image
  refine ⟨e.strictMono, ?_⟩
  intro i j k hij hjk
  have hj0 : (0 : Fin 6) < j := by omega
  have hj5 : j < (5 : Fin 6) := by omega
  rw [hcolor i j k hij hjk hj0 hj5]
  fin_cases j
  · change i.val < 0 at hij
    omega
  · simpa [e] using h1
  · simpa [e] using h2
  · simpa [e] using h3
  · simpa [e] using h4
  · change 5 < k.val at hjk
    omega

/-- The finite middle-word condition saying that at least one but no three of
the four internal positions are right. -/
def StrongSixMiddleWordWeightOneOrTwo {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) : Prop :=
    let e := polygon.orderEmbOfFin hcard
    let c1 := χ ⟨e 0, e 1, e 5, by simp, by simp⟩
    let c2 := χ ⟨e 0, e 2, e 5, by simp, by simp⟩
    let c3 := χ ⟨e 0, e 3, e 5, by simp, by simp⟩
    let c4 := χ ⟨e 0, e 4, e 5, by simp, by simp⟩
    (c1 = Turn.right ∨ c2 = Turn.right ∨ c3 = Turn.right ∨ c4 = Turn.right) ∧
    ¬(c1 = Turn.right ∧ c2 = Turn.right ∧ c3 = Turn.right) ∧
    ¬(c1 = Turn.right ∧ c2 = Turn.right ∧ c4 = Turn.right) ∧
    ¬(c1 = Turn.right ∧ c3 = Turn.right ∧ c4 = Turn.right) ∧
    ¬(c2 = Turn.right ∧ c3 = Turn.right ∧ c4 = Turn.right)

/-- A strong six avoiding a cap five and a cup six has middle-word weight one
or two. -/
theorem strongSix_middle_word_weight_one_or_two
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hnoCap : ¬ContainsCapSet χ polygon 5)
    (hnoCup : ¬ContainsCupSet χ polygon 6) :
    StrongSixMiddleWordWeightOneOrTwo χ polygon hcard := by
  unfold StrongSixMiddleWordWeightOneOrTwo
  dsimp only
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have hsome :
      χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.right ∨
      χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.right ∨
      χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.right ∨
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.right := by
    by_contra hnone
    push Not at hnone
    apply hnoCup
    apply strongSix_all_left_middles_force_cupSix hcard hstrong
    · simpa only [e, Turn.ne_right_iff_eq_left] using hnone.1
    · simpa only [e, Turn.ne_right_iff_eq_left] using hnone.2.1
    · simpa only [e, Turn.ne_right_iff_eq_left] using hnone.2.2.1
    · simpa only [e, Turn.ne_right_iff_eq_left] using hnone.2.2.2
  refine ⟨hsome, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩
    exact hnoCap (strongSix_three_right_middles_force_capFive hcard hstrong
      1 2 3 (by decide) (by decide) (by decide) (by decide) h1 h2 h3)
  · rintro ⟨h1, h2, h4⟩
    exact hnoCap (strongSix_three_right_middles_force_capFive hcard hstrong
      1 2 4 (by decide) (by decide) (by decide) (by decide) h1 h2 h4)
  · rintro ⟨h1, h3, h4⟩
    exact hnoCap (strongSix_three_right_middles_force_capFive hcard hstrong
      1 3 4 (by decide) (by decide) (by decide) (by decide) h1 h3 h4)
  · rintro ⟨h2, h3, h4⟩
    exact hnoCap (strongSix_three_right_middles_force_capFive hcard hstrong
      2 3 4 (by decide) (by decide) (by decide) (by decide) h2 h3 h4)

/-- A right-endpoint failure whose three earlier comparison vertices all lie
on the left side of the cut. This is the localized extreme role for a fresh
left-side vertex extending a crossing polygon. -/
def HasRightEndpointFailureWithLeftCore {n : ℕ} (χ : TripleColoring n)
    (polygon left : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ (i i' j k k' : Fin n)
      (hij : i < j) (hi'j : i' < j) (hjk : j < k) (hjk' : j < k'),
    i ∈ insert q polygon ∧
      i' ∈ insert q polygon ∧
      j ∈ insert q polygon ∧
      k ∈ insert q polygon ∧
      k' ∈ insert q polygon ∧
      MiddleExtensionFailureRole.rightEndpoint.Matches q i i' j k k' ∧
      i ∈ left ∧ i' ∈ left ∧ j ∈ left ∧
      χ ⟨i, j, k, hij, hjk⟩ ≠ χ ⟨i', j, k', hi'j, hjk'⟩

/-- Dually, a left-endpoint failure whose shared middle and two later
comparison vertices all lie on the right side of the cut. -/
def HasLeftEndpointFailureWithRightCore {n : ℕ} (χ : TripleColoring n)
    (polygon right : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ (i i' j k k' : Fin n)
      (hij : i < j) (hi'j : i' < j) (hjk : j < k) (hjk' : j < k'),
    i ∈ insert q polygon ∧
      i' ∈ insert q polygon ∧
      j ∈ insert q polygon ∧
      k ∈ insert q polygon ∧
      k' ∈ insert q polygon ∧
      MiddleExtensionFailureRole.leftEndpoint.Matches q i i' j k k' ∧
      j ∈ right ∧ k ∈ right ∧ k' ∈ right ∧
      χ ⟨i, j, k, hij, hjk⟩ ≠ χ ⟨i', j, k', hi'j, hjk'⟩

/-- If a left-side vertex occurs as the right endpoint of a crossing
polygon's failed comparison, all three earlier vertices of that comparison
are forced onto the left side. -/
theorem rightEndpoint_failure_of_left_vertex_has_left_core
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)} {q : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left ∪ right) (hqLeft : q ∈ left)
    (hfailure : HasMiddleExtensionFailureWithRole χ polygon q
      .rightEndpoint) :
    HasRightEndpointFailureWithLeftCore χ polygon left q := by
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hrole, hneq⟩ := hfailure
  have memPolygon {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x ≠ q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hxq rfl).elim
    · exact hx
  have liesLeft {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x < q) : x ∈ left := by
    have hxPolygon := memPolygon hx (by omega)
    rcases Finset.mem_union.mp (hpolygonSub hxPolygon) with hxLeft | hxRight
    · exact hxLeft
    · have hqx := horder q hqLeft x hxRight
      omega
  have hjq : j < q := by
    rcases hrole with rfl | rfl <;> omega
  exact ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hrole,
    liesLeft hi (hij.trans hjq), liesLeft hi' (hi'j.trans hjq),
    liesLeft hj hjq, hneq⟩

/-- If a right-side vertex occurs as the left endpoint of a crossing
polygon's failed comparison, the three later vertices of that comparison
are forced onto the right side. -/
theorem leftEndpoint_failure_of_right_vertex_has_right_core
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)} {q : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left ∪ right) (hqRight : q ∈ right)
    (hfailure : HasMiddleExtensionFailureWithRole χ polygon q
      .leftEndpoint) :
    HasLeftEndpointFailureWithRightCore χ polygon right q := by
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hrole, hneq⟩ := hfailure
  have memPolygon {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x ≠ q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hxq rfl).elim
    · exact hx
  have liesRight {x : Fin n} (hx : x ∈ insert q polygon)
      (hqx : q < x) : x ∈ right := by
    have hxPolygon := memPolygon hx (by omega)
    rcases Finset.mem_union.mp (hpolygonSub hxPolygon) with hxLeft | hxRight
    · have hxq := horder x hxLeft q hqRight
      omega
    · exact hxRight
  have hqj : q < j := by
    rcases hrole with rfl | rfl <;> omega
  exact ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hrole, liesRight hj hqj,
    liesRight hk (hqj.trans hjk), liesRight hk' (hqj.trans hjk'), hneq⟩

/-- Every failed extension by a left-side vertex has one of two interleaving
roles, or else its right-endpoint role has a fully left-localized core. -/
theorem left_vertex_failure_role_or_left_core
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)} {q : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left ∪ right) (hqLeft : q ∈ left)
    (hfailure : HasMiddleExtensionFailure χ polygon q) :
    HasMiddleExtensionFailureWithRole χ polygon q .leftEndpoint ∨
      HasMiddleExtensionFailureWithRole χ polygon q .middle ∨
      HasRightEndpointFailureWithLeftCore χ polygon left q := by
  obtain ⟨role, hrole⟩ :=
    hasMiddleExtensionFailure_iff_exists_role.mp hfailure
  cases role with
  | leftEndpoint => exact Or.inl hrole
  | middle => exact Or.inr (Or.inl hrole)
  | rightEndpoint => exact Or.inr (Or.inr
      (rightEndpoint_failure_of_left_vertex_has_left_core
        horder hpolygonSub hqLeft hrole))

/-- Every failed extension by a right-side vertex has one of two interleaving
roles, or else its left-endpoint role has a fully right-localized core. -/
theorem right_vertex_failure_role_or_right_core
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)} {q : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hpolygonSub : polygon ⊆ left ∪ right) (hqRight : q ∈ right)
    (hfailure : HasMiddleExtensionFailure χ polygon q) :
    HasLeftEndpointFailureWithRightCore χ polygon right q ∨
      HasMiddleExtensionFailureWithRole χ polygon q .middle ∨
      HasMiddleExtensionFailureWithRole χ polygon q .rightEndpoint := by
  obtain ⟨role, hrole⟩ :=
    hasMiddleExtensionFailure_iff_exists_role.mp hfailure
  cases role with
  | leftEndpoint => exact Or.inl (
      leftEndpoint_failure_of_right_vertex_has_right_core horder hpolygonSub
        hqRight hrole)
  | middle => exact Or.inr (Or.inl hrole)
  | rightEndpoint => exact Or.inr (Or.inr hrole)

/-- The side-aware finite state of a failed extension across an ordered cut.
On the vertex's own side, the extreme role pointing back across the cut is
replaced by the stronger conclusion that its comparison core is local. -/
def HasCutLocalizedMiddleFailure {n : ℕ} (χ : TripleColoring n)
    (left right polygon : Finset (Fin n)) (q : Fin n) : Prop :=
  (q ∈ left →
    HasMiddleExtensionFailureWithRole χ polygon q .leftEndpoint ∨
      HasMiddleExtensionFailureWithRole χ polygon q .middle ∨
      HasRightEndpointFailureWithLeftCore χ polygon left q) ∧
  (q ∈ right →
    HasLeftEndpointFailureWithRightCore χ polygon right q ∨
      HasMiddleExtensionFailureWithRole χ polygon q .middle ∨
      HasMiddleExtensionFailureWithRole χ polygon q .rightEndpoint)

/-- All twelve directed failures of a mutually obstructed pair have the
side-aware three-state normalization. This remains valid for every proper
crossing split, including the residual `3+3` case. -/
theorem mutuallyMiddleObstructedPair_has_cutLocalized_failures
    {n : ℕ} {χ : TripleColoring n}
    {left right first second : Finset (Fin n)}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hfirstSub : first ⊆ left ∪ right)
    (hsecondSub : second ⊆ left ∪ right)
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second) :
    (∀ q ∈ second,
      HasCutLocalizedMiddleFailure χ left right first q) ∧
    (∀ q ∈ first,
      HasCutLocalizedMiddleFailure χ left right second q) := by
  constructor
  · intro q hqSecond
    have hfailure := hmutual.2.2.2.2.2.1 q hqSecond
    constructor
    · intro hqLeft
      exact left_vertex_failure_role_or_left_core horder hfirstSub hqLeft
        hfailure
    · intro hqRight
      exact right_vertex_failure_role_or_right_core horder hfirstSub hqRight
        hfailure
  · intro q hqFirst
    have hfailure := hmutual.2.2.2.2.2.2 q hqFirst
    constructor
    · intro hqLeft
      exact left_vertex_failure_role_or_left_core horder hsecondSub hqLeft
        hfailure
    · intro hqRight
      exact right_vertex_failure_role_or_right_core horder hsecondSub hqRight
        hfailure

/-- Honest transition from any packed strong six: deleting it yields a
disjoint, mutually middle-obstructed strong-six partner with one of the five
proper crossing splits. -/
theorem packedStrongSix_has_mutuallyObstructed_split_partner
    {n : ℕ} {χ : TripleColoring n} {left right first : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hfirstSub : first ⊆ left ∪ right) (hfirstCard : first.card = 6)
    (hfirstStrong : IsStrongPolygonSet χ first)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    ∃ second : Finset (Fin n), second ⊆ left ∪ right ∧
      MutuallyMiddleObstructedStrongSixPair χ first second ∧
      (((second ∩ left).card = 1 ∧ (second ∩ right).card = 5) ∨
       ((second ∩ left).card = 2 ∧ (second ∩ right).card = 4) ∨
       ((second ∩ left).card = 3 ∧ (second ∩ right).card = 3) ∨
       ((second ∩ left).card = 4 ∧ (second ∩ right).card = 2) ∨
       ((second ∩ left).card = 5 ∧ (second ∩ right).card = 1)) := by
  obtain ⟨second, hsecondSub, hmutual⟩ :=
    exists_mutuallyMiddleObstructed_partner hpacking hfirstSub hfirstCard
      hfirstStrong hnoStrongSeven
  have hsplit := strongSix_has_proper_crossing_split hdisjoint hsecondSub
    hmutual.2.2.1 hmutual.2.2.2.2.1 hnoLeftStrong hnoRightStrong
  exact ⟨second, hsecondSub, hmutual, hsplit⟩

/-- Under the ambient `(5,6,7)` exclusions, the deleted strong six and its
packed partner both have weight-one-or-two middle words. The partner is
mutually obstructed and has one of the five explicit crossing splits. -/
theorem packedStrongSix_has_bounded_mutuallyObstructed_partner
    {n : ℕ} {χ : TripleColoring n} {left right first : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (hfirstSub : first ⊆ left ∪ right) (hfirstCard : first.card = 6)
    (hfirstStrong : IsStrongPolygonSet χ first)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hnoCapFive : ¬ContainsCapSet χ (left ∪ right) 5)
    (hnoCupSix : ¬ContainsCupSet χ (left ∪ right) 6)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    StrongSixMiddleWordWeightOneOrTwo χ first hfirstCard ∧
    ∃ (second : Finset (Fin n)) (_hsecondSub : second ⊆ left ∪ right)
        (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second),
      StrongSixMiddleWordWeightOneOrTwo χ second hmutual.2.2.1 ∧
      (((second ∩ left).card = 1 ∧ (second ∩ right).card = 5) ∨
       ((second ∩ left).card = 2 ∧ (second ∩ right).card = 4) ∨
       ((second ∩ left).card = 3 ∧ (second ∩ right).card = 3) ∨
       ((second ∩ left).card = 4 ∧ (second ∩ right).card = 2) ∨
       ((second ∩ left).card = 5 ∧ (second ∩ right).card = 1)) := by
  have hfirstNoCap : ¬ContainsCapSet χ first 5 := fun hcap ↦
    hnoCapFive (FinsetPolygon.ContainsCapSet.mono hcap hfirstSub)
  have hfirstNoCup : ¬ContainsCupSet χ first 6 := fun hcup ↦
    hnoCupSix (FinsetPolygon.ContainsCupSet.mono hcup hfirstSub)
  have hfirstWord := strongSix_middle_word_weight_one_or_two
    hfirstCard hfirstStrong hfirstNoCap hfirstNoCup
  obtain ⟨second, hsecondSub, hmutual, hsplit⟩ :=
    packedStrongSix_has_mutuallyObstructed_split_partner hdisjoint hfirstSub
      hfirstCard hfirstStrong hpacking hnoLeftStrong hnoRightStrong
      hnoStrongSeven
  have hsecondCard : second.card = 6 := hmutual.2.2.1
  have hsecondStrong : IsStrongPolygonSet χ second := hmutual.2.2.2.2.1
  have hsecondNoCap : ¬ContainsCapSet χ second 5 := fun hcap ↦
    hnoCapFive (FinsetPolygon.ContainsCapSet.mono hcap hsecondSub)
  have hsecondNoCup : ¬ContainsCupSet χ second 6 := fun hcup ↦
    hnoCupSix (FinsetPolygon.ContainsCupSet.mono hcup hsecondSub)
  have hsecondWord := strongSix_middle_word_weight_one_or_two
    hsecondCard hsecondStrong hsecondNoCap hsecondNoCup
  exact ⟨hfirstWord, second, hsecondSub, hmutual, hsecondWord, hsplit⟩

end ErdosSzekeres

end
