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

/-- A right-endpoint extension anomaly at a nonfinal polygon middle. -/
def HasInternalRightEndpointMiddleAnomaly {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  ∃ (i j : Fin n) (hij : i < j) (hjq : j < q)
      (hfirst : e 0 < j) (hlast : j < e 5),
    i ∈ polygon ∧ j ∈ polygon ∧
      χ ⟨i, j, q, hij, hjq⟩ ≠ χ ⟨e 0, j, e 5, hfirst, hlast⟩

/-- The exceptional right-endpoint anomaly whose shared middle is the final
polygon vertex. -/
def HasFinalMiddleFanVariation {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  ∃ (i i' : Fin n) (hi : i < e 5) (hi' : i' < e 5)
      (hlastq : e 5 < q),
    i ∈ polygon ∧ i' ∈ polygon ∧
      χ ⟨i, e 5, q, hi, hlastq⟩ ≠
        χ ⟨i', e 5, q, hi', hlastq⟩

/-- A forced right-endpoint failure relative to a strong six-set normalizes
to one of four internally referenced middle anomalies or to a variation in
the final-middle fan. -/
theorem rightEndpoint_failure_internal_or_final
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)}
    {q : Fin n} (hcard : polygon.card = 6)
    (hstrong : IsStrongPolygonSet χ polygon)
    (hafter : ∀ x ∈ polygon, x < q)
    (hfailure : HasMiddleExtensionFailureWithRole χ polygon q
      .rightEndpoint) :
    HasInternalRightEndpointMiddleAnomaly χ polygon hcard q ∨
      HasFinalMiddleFanVariation χ polygon hcard q := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (r : Fin 6) : e r ∈ polygon :=
    polygon.orderEmbOfFin_mem hcard r
  have heImage : Finset.univ.image e = polygon :=
    Finset.image_orderEmbOfFin_univ polygon hcard
  have indexOfMem {x : Fin n} (hx : x ∈ polygon) : ∃ r : Fin 6, e r = x := by
    have hxImage : x ∈ Finset.univ.image e := by simpa [heImage] using hx
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hxImage
  have leLast {x : Fin n} (hx : x ∈ polygon) : x ≤ e 5 := by
    obtain ⟨r, rfl⟩ := indexOfMem hx
    exact e.monotone (Fin.le_last r)
  have firstLe {x : Fin n} (hx : x ∈ polygon) : e 0 ≤ x := by
    obtain ⟨r, rfl⟩ := indexOfMem hx
    exact e.monotone (Fin.zero_le r)
  have memberLeQ {x : Fin n} (hx : x ∈ insert q polygon) : x ≤ q := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact (hafter x hx).le
  have memPolygonOfLt {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x < q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (lt_irrefl _ hxq).elim
    · exact hx
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hrole, hneq⟩ := hfailure
  have hjq : j < q := hjk.trans_le (memberLeQ hk)
  have hiq : i < q := hij.trans hjq
  have hi'q : i' < q := hi'j.trans hjq
  have hiPolygon := memPolygonOfLt hi hiq
  have hi'Polygon := memPolygonOfLt hi' hi'q
  have hjPolygon := memPolygonOfLt hj hjq
  have hfirst : e 0 < j := (firstLe hiPolygon).trans_lt hij
  have hlastLe : j ≤ e 5 := leLast hjPolygon
  by_cases hjLast : j = e 5
  · have hkq : k = q := by
      rcases Finset.mem_insert.mp hk with rfl | hkPolygon
      · rfl
      · have := leLast hkPolygon
        omega
    have hk'q : k' = q := by
      rcases Finset.mem_insert.mp hk' with rfl | hkPolygon
      · rfl
      · have := leLast hkPolygon
        omega
    exact Or.inr ⟨i, i', by simpa [hjLast] using hij,
      by simpa [hjLast] using hi'j, by simpa [hjLast] using hjq,
      hiPolygon, hi'Polygon, by simpa [hjLast, hkq, hk'q] using hneq⟩
  · have hlast : j < e 5 := lt_of_le_of_ne hlastLe hjLast
    have hmiddle : IsMiddleDeterminedOn χ polygon :=
      FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
    by_cases hkq : k = q
    · by_cases hk'q : k' = q
      · by_cases hfirstDiff :
          χ ⟨i, j, q, hij, hjq⟩ ≠ χ ⟨e 0, j, e 5, hfirst, hlast⟩
        · exact Or.inl ⟨i, j, hij, hjq, hfirst, hlast,
            hiPolygon, hjPolygon, hfirstDiff⟩
        · have hsecondDiff :
            χ ⟨i', j, q, hi'j, hjq⟩ ≠
              χ ⟨e 0, j, e 5, hfirst, hlast⟩ := by
            intro heq
            apply hneq
            simpa [hkq, hk'q] using
              (not_ne_iff.mp hfirstDiff).trans heq.symm
          exact Or.inl ⟨i', j, hi'j, hjq, hfirst, hlast,
            hi'Polygon, hjPolygon, hsecondDiff⟩
      · have hk'Polygon : k' ∈ polygon := by
          rcases Finset.mem_insert.mp hk' with hk'q'' | hk'Polygon
          · exact (hk'q hk'q'').elim
          · exact hk'Polygon
        have hpolygonEq :
            χ ⟨i', j, k', hi'j, hjk'⟩ =
              χ ⟨e 0, j, e 5, hfirst, hlast⟩ :=
          hmiddle hi'j hfirst hjk' hlast hi'Polygon (heMem 0)
            hjPolygon hk'Polygon (heMem 5)
        exact Or.inl ⟨i, j, hij, hjq, hfirst, hlast,
          hiPolygon, hjPolygon, by simpa [hkq, hpolygonEq] using hneq⟩
    · have hk'q : k' = q := hrole.resolve_left hkq
      have hkPolygon : k ∈ polygon := by
        rcases Finset.mem_insert.mp hk with hkq' | hkPolygon
        · exact (hkq hkq').elim
        · exact hkPolygon
      have hpolygonEq :
          χ ⟨i, j, k, hij, hjk⟩ =
            χ ⟨e 0, j, e 5, hfirst, hlast⟩ :=
        hmiddle hij hfirst hjk hlast hiPolygon (heMem 0)
          hjPolygon hkPolygon (heMem 5)
      exact Or.inl ⟨i', j, hi'j, hjq, hfirst, hlast,
        hi'Polygon, hjPolygon, by
          intro heq
          apply hneq
          simpa [hk'q] using hpolygonEq.trans heq.symm⟩

/-- A change in the final-middle fan between two polygon vertices forces both
the earlier fan color and the intervening bridge color to equal the strong
polygon's reference color at the later middle vertex. -/
theorem finalMiddleFan_variation_forces_later_middle_color
    {n : ℕ} {χ : TripleColoring n} {ambient polygon : Finset (Fin n)}
    {q : Fin n} (hcard : polygon.card = 6)
    (hpolygonSub : polygon ⊆ ambient)
    (hstrong : IsStrongPolygonSet χ polygon)
    (hqAmbient : q ∈ ambient) (hafter : ∀ x ∈ polygon, x < q)
    (hone : OneChangeOn χ ambient)
    {a b : Fin 6} (hab : a < b) (hb5 : b < (5 : Fin 6))
    (hvariation :
      χ ⟨polygon.orderEmbOfFin hcard a, polygon.orderEmbOfFin hcard 5, q,
        (polygon.orderEmbOfFin hcard).strictMono (hab.trans hb5),
        hafter _ (polygon.orderEmbOfFin_mem hcard 5)⟩ ≠
      χ ⟨polygon.orderEmbOfFin hcard b, polygon.orderEmbOfFin hcard 5, q,
        (polygon.orderEmbOfFin hcard).strictMono hb5,
        hafter _ (polygon.orderEmbOfFin_mem hcard 5)⟩) :
    let e := polygon.orderEmbOfFin hcard
    χ ⟨e a, e 5, q, e.strictMono (hab.trans hb5),
        hafter _ (polygon.orderEmbOfFin_mem hcard 5)⟩ =
      χ ⟨e 0, e b, e 5, e.strictMono (by omega),
        e.strictMono hb5⟩ ∧
    χ ⟨e a, e b, q, e.strictMono hab,
        (e.strictMono hb5).trans
          (hafter _ (polygon.orderEmbOfFin_mem hcard 5))⟩ =
      χ ⟨e 0, e b, e 5, e.strictMono (by omega),
        e.strictMono hb5⟩ := by
  dsimp only
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (r : Fin 6) : e r ∈ polygon :=
    polygon.orderEmbOfFin_mem hcard r
  have hallowed := hone (e.strictMono hab) (e.strictMono hb5)
    (hafter _ (heMem 5))
    (hpolygonSub (heMem a)) (hpolygonSub (heMem b))
    (hpolygonSub (heMem 5)) hqAmbient
  have hhead := hallowed.head_eq_of_third_ne_fourth (by
    simpa [e] using hvariation)
  have hmiddle : IsMiddleDeterminedOn χ polygon :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
  have hb0 : (0 : Fin 6) < b := by omega
  have hreference :
      χ ⟨e a, e b, e 5, e.strictMono hab, e.strictMono hb5⟩ =
        χ ⟨e 0, e b, e 5, e.strictMono hb0,
          e.strictMono hb5⟩ :=
    hmiddle (e.strictMono hab) (e.strictMono hb0)
      (e.strictMono hb5) (e.strictMono hb5)
      (heMem a) (heMem 0) (heMem b) (heMem 5) (heMem 5)
  exact ⟨hhead.2.symm.trans (hhead.1.symm.trans hreference),
    hhead.1.symm.trans hreference⟩

end ErdosSzekeres

end
