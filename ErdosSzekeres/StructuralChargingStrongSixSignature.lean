module

public import ErdosSzekeres.StructuralChargingCapFreeSides

@[expose] public section

/-!
# Strong-six middle signatures

A strong ordered set is colored by its middle vertices.  On six vertices a
four-cap-free, six-cup-free strong set therefore has exactly one right-colored
internal middle position.  This file packages that four-way classification
for the remaining structural-charging branch.
-/

namespace ErdosSzekeres

set_option maxHeartbeats 0

/-- The four reference colors of a strong six-set have exactly one right
entry. -/
theorem strongSix_exactly_one_right_middle
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hnoCap : ¬ContainsCapSet χ polygon 4)
    (hnoCup : ¬ContainsCupSet χ polygon 6) :
    let e := polygon.orderEmbOfFin hcard
    (χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.left ∧
      χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.left ∧
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.left) ∨
    (χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.left ∧
      χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.left ∧
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.left) ∨
    (χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.left ∧
      χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.left ∧
      χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.left) ∨
    (χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.left ∧
      χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.left ∧
      χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.left ∧
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
        χ ⟨e 0, e j, e 5, e.strictMono hj0, e.strictMono hj5⟩ := by
    exact hmiddle (e.strictMono hij) (e.strictMono hj0)
      (e.strictMono hjk) (e.strictMono hj5)
      (heMem i) (heMem 0) (heMem j) (heMem k) (heMem 5)
  have cap_of_pair (a b : Fin 6)
      (ha0 : (0 : Fin 6) < a) (hab : a < b) (hb5 : b < (5 : Fin 6))
      (ha : χ ⟨e 0, e a, e 5, e.strictMono ha0,
          e.strictMono (hab.trans hb5)⟩ = Turn.right)
      (hb : χ ⟨e 0, e b, e 5, e.strictMono (ha0.trans hab),
          e.strictMono hb5⟩ = Turn.right) :
      ContainsCapSet χ polygon 4 := by
    let g : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono
      ![e 0, e a, e b, e 5] (by
        intro i j hij
        fin_cases i <;> fin_cases j
        all_goals (try norm_num at hij)
        all_goals first
          | exact e.strictMono ha0
          | exact e.strictMono (ha0.trans hab)
          | exact e.strictMono (ha0.trans (hab.trans hb5))
          | exact e.strictMono hab
          | exact e.strictMono (hab.trans hb5)
          | exact e.strictMono hb5)
    have hgSub : Finset.univ.image g ⊆ polygon := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      fin_cases i <;> simp [g, heMem]
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
      · simpa [g] using
          (hcolor 0 a b ha0 hab ha0 (hab.trans hb5)).trans ha
      · simpa [g] using
          (hcolor 0 a 5 ha0 (hab.trans hb5) ha0
            (hab.trans hb5)).trans ha
    · change i.val < 2 at hij
      change 2 < k.val at hjk
      have hk : k = 3 := by omega
      subst k
      have hi : i = 0 ∨ i = 1 := by omega
      rcases hi with rfl | rfl
      · simpa [g] using
          (hcolor 0 b 5 (ha0.trans hab) hb5
            (ha0.trans hab) hb5).trans hb
      · simpa [g] using
          (hcolor a b 5 hab hb5 (ha0.trans hab) hb5).trans hb
    · change 3 < k.val at hjk
      omega
  have cup_of_all_left
      (h1 : χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.left)
      (h2 : χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.left)
      (h3 : χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.left)
      (h4 : χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.left) :
      ContainsCupSet χ polygon 6 := by
    have heImage : Finset.univ.image e = polygon :=
      Finset.image_orderEmbOfFin_univ polygon hcard
    refine ⟨polygon, Finset.Subset.rfl, hcard, ?_⟩
    rw [← heImage]
    apply FinsetPolygon.IsCup.image
    refine ⟨e.strictMono, ?_⟩
    intro i j k hij hjk
    have hj0 : (0 : Fin 6) < j := by omega
    have hj5 : j < (5 : Fin 6) := by omega
    rw [hcolor i j k hij hjk hj0 hj5]
    fin_cases j
    · change 0 < 0 at hj0
      omega
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · simpa using h4
    · change 5 < 5 at hj5
      omega
  have h12 : ¬(χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.right) := by
    rintro ⟨h1, h2⟩
    exact hnoCap (cap_of_pair 1 2 (by decide) (by decide) (by decide) h1 h2)
  have h13 : ¬(χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.right) := by
    rintro ⟨h1, h3⟩
    exact hnoCap (cap_of_pair 1 3 (by decide) (by decide) (by decide) h1 h3)
  have h14 : ¬(χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.right) := by
    rintro ⟨h1, h4⟩
    exact hnoCap (cap_of_pair 1 4 (by decide) (by decide) (by decide) h1 h4)
  have h23 : ¬(χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.right) := by
    rintro ⟨h2, h3⟩
    exact hnoCap (cap_of_pair 2 3 (by decide) (by decide) (by decide) h2 h3)
  have h24 : ¬(χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.right) := by
    rintro ⟨h2, h4⟩
    exact hnoCap (cap_of_pair 2 4 (by decide) (by decide) (by decide) h2 h4)
  have h34 : ¬(χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.right ∧
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.right) := by
    rintro ⟨h3, h4⟩
    exact hnoCap (cap_of_pair 3 4 (by decide) (by decide) (by decide) h3 h4)
  have hsome :
      χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = Turn.right ∨
      χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = Turn.right ∨
      χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = Turn.right ∨
      χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = Turn.right := by
    by_contra h
    push Not at h
    apply hnoCup
    apply cup_of_all_left
    all_goals cases hcolor : χ _ <;> simp_all
  generalize hc1 : χ ⟨e 0, e 1, e 5, by simp, by simp⟩ = c1 at *
  generalize hc2 : χ ⟨e 0, e 2, e 5, by simp, by simp⟩ = c2 at *
  generalize hc3 : χ ⟨e 0, e 3, e 5, by simp, by simp⟩ = c3 at *
  generalize hc4 : χ ⟨e 0, e 4, e 5, by simp, by simp⟩ = c4 at *
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp_all

end ErdosSzekeres

end
