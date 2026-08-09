module

public import ErdosSzekeres.StructuralChargingNextState578Bracket

@[expose] public section

/-!
# Endpoint-to-bracket interface at state `(5,7,8)`

The common-minimum endpoint law only says that the two sweep-middle vertices
of a four-cup lie in the lower child.  This file records the exact extra datum
needed by the surviving bracket theorem: both sweep endpoints must lie in the
upper child.  It also keeps the complementary one-upper-endpoint alternative
explicit rather than silently treating every lower-endpoint cup as a bracket.
-/

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

/-- The vertices of `lower` which lie strictly between two sweep vertices. -/
def lowerBracket578 {n : ℕ} (lower : Finset (Fin n)) (left right : Fin n) :
    Finset (Fin n) :=
  lower.filter fun x ↦ left < x ∧ x < right

/-- Vertices of a finite set strictly below a sweep pivot. -/
def belowPivot578 {n : ℕ} (support : Finset (Fin n)) (pivot : Fin n) :
    Finset (Fin n) :=
  support.filter fun x ↦ x < pivot

/-- Vertices of a finite set strictly above a sweep pivot. -/
def abovePivot578 {n : ℕ} (support : Finset (Fin n)) (pivot : Fin n) :
    Finset (Fin n) :=
  support.filter fun x ↦ pivot < x

@[simp]
theorem mem_lowerBracket578 {n : ℕ} {lower : Finset (Fin n)} {left right x : Fin n} :
    x ∈ lowerBracket578 lower left right ↔ x ∈ lower ∧ left < x ∧ x < right := by
  simp [lowerBracket578]

theorem lowerBracket578_subset {n : ℕ} (lower : Finset (Fin n)) (left right : Fin n) :
    lowerBracket578 lower left right ⊆ lower := by
  intro x hx
  exact (mem_lowerBracket578.mp hx).1

@[simp]
theorem mem_belowPivot578 {n : ℕ} {support : Finset (Fin n)} {pivot x : Fin n} :
    x ∈ belowPivot578 support pivot ↔ x ∈ support ∧ x < pivot := by
  simp [belowPivot578]

@[simp]
theorem mem_abovePivot578 {n : ℕ} {support : Finset (Fin n)} {pivot x : Fin n} :
    x ∈ abovePivot578 support pivot ↔ x ∈ support ∧ pivot < x := by
  simp [abovePivot578]

/-- A lower-endpoint four-cup with exactly one sweep endpoint certified in the
upper child. -/
def CupFourOneUpperEndpointShape578
    {n : ℕ} (cup lower upper : Finset (Fin n)) : Prop :=
  ∃ hcard : cup.card = 4,
    let c := cup.orderEmbOfFin hcard
    c 1 ∈ lower ∧ c 2 ∈ lower ∧
      ((c 0 ∈ upper ∧ c 3 ∈ lower) ∨ (c 0 ∈ lower ∧ c 3 ∈ upper))

/-- A four-cup whose two sweep endpoints are upper and whose two sweep-middle
vertices are lower.  Its endpoints form an actual bracket. -/
def CupFourTwoUpperBracketShape578
    {n : ℕ} (cup lower upper : Finset (Fin n)) : Prop :=
  ∃ hcard : cup.card = 4,
    let c := cup.orderEmbOfFin hcard
    c 0 ∈ upper ∧ c 3 ∈ upper ∧ c 1 ∈ lower ∧ c 2 ∈ lower

private theorem four_subset_of_orderEmbOfFin_mem
    {n : ℕ} {four target : Finset (Fin n)} (hcard : four.card = 4)
    (h0 : four.orderEmbOfFin hcard 0 ∈ target)
    (h1 : four.orderEmbOfFin hcard 1 ∈ target)
    (h2 : four.orderEmbOfFin hcard 2 ∈ target)
    (h3 : four.orderEmbOfFin hcard 3 ∈ target) :
    four ⊆ target := by
  intro x hx
  rw [← Finset.image_orderEmbOfFin_univ four hcard] at hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  fin_cases i <;> assumption

/-- A lower-endpoint cup which is local to the split but not wholly lower has
one or two upper sweep endpoints.  The endpoint law alone does not select the
two-endpoint bracket branch. -/
theorem CupFourLowerEndpointShape578.oneUpper_or_twoUpper
    {n : ℕ} {cup lower upper : Finset (Fin n)}
    (hshape : CupFourLowerEndpointShape578 cup lower upper)
    (hcupSub : cup ⊆ lower ∪ upper) (hnotLower : ¬cup ⊆ lower) :
    CupFourOneUpperEndpointShape578 cup lower upper ∨
      CupFourTwoUpperBracketShape578 cup lower upper := by
  rcases hshape with ⟨hcard, hmiddleOne, hmiddleTwo, _⟩
  let c := cup.orderEmbOfFin hcard
  have hzero : c 0 ∈ lower ∨ c 0 ∈ upper :=
    Finset.mem_union.mp (hcupSub (cup.orderEmbOfFin_mem hcard 0))
  have hthree : c 3 ∈ lower ∨ c 3 ∈ upper :=
    Finset.mem_union.mp (hcupSub (cup.orderEmbOfFin_mem hcard 3))
  rcases hzero with hzeroLower | hzeroUpper
  · rcases hthree with hthreeLower | hthreeUpper
    · exact (hnotLower (four_subset_of_orderEmbOfFin_mem hcard
        hzeroLower hmiddleOne hmiddleTwo hthreeLower)).elim
    · exact Or.inl ⟨hcard, hmiddleOne, hmiddleTwo,
        Or.inr ⟨hzeroLower, hthreeUpper⟩⟩
  · rcases hthree with hthreeLower | hthreeUpper
    · exact Or.inl ⟨hcard, hmiddleOne, hmiddleTwo,
        Or.inl ⟨hzeroUpper, hthreeLower⟩⟩
    · exact Or.inr ⟨hcard, hzeroUpper, hthreeUpper,
        hmiddleOne, hmiddleTwo⟩

/-- A split child with at most one vertex eliminates the genuine bracket
alternative, leaving exactly one upper sweep endpoint. -/
theorem CupFourLowerEndpointShape578.oneUpper_of_upper_card_le_one
    {n : ℕ} {cup lower upper : Finset (Fin n)}
    (hshape : CupFourLowerEndpointShape578 cup lower upper)
    (hcupSub : cup ⊆ lower ∪ upper) (hnotLower : ¬cup ⊆ lower)
    (hupperCard : upper.card ≤ 1) :
    CupFourOneUpperEndpointShape578 cup lower upper := by
  rcases hshape.oneUpper_or_twoUpper hcupSub hnotLower with hone | htwo
  · exact hone
  · rcases htwo with ⟨hcard, hzeroUpper, hthreeUpper, _, _⟩
    have hne : cup.orderEmbOfFin hcard (0 : Fin 4) ≠
        cup.orderEmbOfFin hcard (3 : Fin 4) :=
      (cup.orderEmbOfFin hcard).injective.ne (by decide)
    have hpairCard :
        ({cup.orderEmbOfFin hcard 0,
          cup.orderEmbOfFin hcard 3} : Finset (Fin n)).card = 2 := by
      simp [hne]
    have hpairSub :
        ({cup.orderEmbOfFin hcard 0,
          cup.orderEmbOfFin hcard 3} : Finset (Fin n)) ⊆ upper := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hzeroUpper
      · exact hthreeUpper
    have htwoLe := Finset.card_le_card hpairSub
    omega

/-- The sweep-middle pair of a two-upper-endpoint cup lies in its actual lower
bracket. -/
theorem CupFourTwoUpperBracketShape578.middlePair_subset_lowerBracket
    {n : ℕ} {cup lower upper : Finset (Fin n)}
    (hshape : CupFourTwoUpperBracketShape578 cup lower upper) :
    ∃ hcard : cup.card = 4,
      sweepMiddlePair578 cup hcard ⊆
        lowerBracket578 lower (cup.orderEmbOfFin hcard 0)
          (cup.orderEmbOfFin hcard 3) := by
  rcases hshape with ⟨hcard, _, _, hmiddleOne, hmiddleTwo⟩
  refine ⟨hcard, ?_⟩
  intro x hx
  simp only [sweepMiddlePair578, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact mem_lowerBracket578.mpr ⟨hmiddleOne,
      (cup.orderEmbOfFin hcard).strictMono (by decide),
      (cup.orderEmbOfFin hcard).strictMono (by decide)⟩
  · exact mem_lowerBracket578.mpr ⟨hmiddleTwo,
      (cup.orderEmbOfFin hcard).strictMono (by decide),
      (cup.orderEmbOfFin hcard).strictMono (by decide)⟩

/-- Every lower vertex of a genuine two-upper-endpoint cup lies strictly
between its upper endpoints. -/
theorem CupFourTwoUpperBracketShape578.mem_lowerBracket_of_mem_lower
    {n : ℕ} {cup lower upper : Finset (Fin n)}
    (hshape : CupFourTwoUpperBracketShape578 cup lower upper)
    (hdisjoint : Disjoint lower upper) {x : Fin n}
    (hxCup : x ∈ cup) (hxLower : x ∈ lower) :
    ∃ hcard : cup.card = 4,
      x ∈ lowerBracket578 lower (cup.orderEmbOfFin hcard 0)
        (cup.orderEmbOfFin hcard 3) := by
  rcases hshape with ⟨hcard, hzeroUpper, hthreeUpper,
    hmiddleOne, hmiddleTwo⟩
  refine ⟨hcard, ?_⟩
  rw [← Finset.image_orderEmbOfFin_univ cup hcard] at hxCup
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxCup
  fin_cases i
  · exact ((Finset.disjoint_left.mp hdisjoint) hxLower hzeroUpper).elim
  · exact mem_lowerBracket578.mpr ⟨hmiddleOne,
      (cup.orderEmbOfFin hcard).strictMono (by decide),
      (cup.orderEmbOfFin hcard).strictMono (by decide)⟩
  · exact mem_lowerBracket578.mpr ⟨hmiddleTwo,
      (cup.orderEmbOfFin hcard).strictMono (by decide),
      (cup.orderEmbOfFin hcard).strictMono (by decide)⟩
  · exact ((Finset.disjoint_left.mp hdisjoint) hxLower hthreeUpper).elim

/-- Every two-upper-endpoint cup certifies at least two vertices in its lower
bracket. -/
theorem CupFourTwoUpperBracketShape578.two_le_lowerBracket_card
    {n : ℕ} {cup lower upper : Finset (Fin n)}
    (hshape : CupFourTwoUpperBracketShape578 cup lower upper) :
    ∃ hcard : cup.card = 4,
      2 ≤ (lowerBracket578 lower (cup.orderEmbOfFin hcard 0)
        (cup.orderEmbOfFin hcard 3)).card := by
  obtain ⟨hcard, hmiddleSub⟩ := hshape.middlePair_subset_lowerBracket
  refine ⟨hcard, ?_⟩
  have hle := Finset.card_le_card hmiddleSub
  rw [sweepMiddlePair578_card] at hle
  exact hle

/-- The existing bracket theorem in the canonical filtered-set notation. -/
theorem HasDeepBelowSplit.lowerBracket578_card_le_six
    {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)} {left right : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hleftUpper : left ∈ upper) (hrightUpper : right ∈ upper)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 5)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 7) :
    (lowerBracket578 lower left right).card ≤ 6 := by
  apply hdeep.bracketed_lower_card_le_six
      (lowerBracket578_subset lower left right) hleftUpper hrightUpper
  · intro x hx
    exact (mem_lowerBracket578.mp hx).2
  · exact hnoCup
  · exact hnoCap

end ErdosSzekeres

end
