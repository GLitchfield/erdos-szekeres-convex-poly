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

/-- A right-endpoint fan variation at an internal polygon middle. Unlike the
earlier final-fan predicate, this form allows the fresh vertex to interleave
with a crossing polygon. -/
def HasInternalRightEndpointFanVariation {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  ∃ (i i' j : Fin n) (hij : i < j) (hi'j : i' < j) (hjq : j < q)
      (_hfirst : e 0 < j) (_hlast : j < e 5),
    i ∈ polygon ∧ i' ∈ polygon ∧ j ∈ polygon ∧
      χ ⟨i, j, q, hij, hjq⟩ ≠ χ ⟨i', j, q, hi'j, hjq⟩

/-- A left-endpoint anomaly at an internal polygon middle, measured against
the polygon's reference color at that middle. -/
def HasInternalLeftEndpointMiddleAnomaly {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  ∃ (j k : Fin n) (hqj : q < j) (hjk : j < k)
      (hfirst : e 0 < j) (hlast : j < e 5),
    j ∈ polygon ∧ k ∈ polygon ∧
      χ ⟨q, j, k, hqj, hjk⟩ ≠ χ ⟨e 0, j, e 5, hfirst, hlast⟩

/-- A left-endpoint fan variation at an internal polygon middle, allowing the
fresh vertex to interleave with a crossing polygon. -/
def HasInternalLeftEndpointFanVariation {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  ∃ (j k k' : Fin n) (hqj : q < j) (hjk : j < k) (hjk' : j < k')
      (_hfirst : e 0 < j) (_hlast : j < e 5),
    j ∈ polygon ∧ k ∈ polygon ∧ k' ∈ polygon ∧
      χ ⟨q, j, k, hqj, hjk⟩ ≠ χ ⟨q, j, k', hqj, hjk'⟩

/-- The boundary fan variation when a fresh left endpoint compares two
triples whose shared middle is the first polygon vertex. -/
def HasFirstMiddleFanVariation {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = 6) (q : Fin n) : Prop :=
  let e := polygon.orderEmbOfFin hcard
  ∃ (k k' : Fin n) (hqfirst : q < e 0) (hfirstk : e 0 < k)
      (hfirstk' : e 0 < k'),
    k ∈ polygon ∧ k' ∈ polygon ∧
      χ ⟨q, e 0, k, hqfirst, hfirstk⟩ ≠
        χ ⟨q, e 0, k', hqfirst, hfirstk'⟩

/-- A failed comparison whose fresh vertex is itself the shared middle. All
four endpoints then belong to the reference polygon. -/
def HasFreshMiddleFanVariation {n : ℕ} (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (q : Fin n) : Prop :=
  ∃ (i i' k k' : Fin n) (hiq : i < q) (hi'q : i' < q)
      (hqk : q < k) (hqk' : q < k'),
    i ∈ polygon ∧ i' ∈ polygon ∧ k ∈ polygon ∧ k' ∈ polygon ∧
      χ ⟨i, q, k, hiq, hqk⟩ ≠ χ ⟨i', q, k', hi'q, hqk'⟩

/-- A fresh shared-middle role is exactly a fan variation whose four
endpoints lie in the original polygon. -/
theorem middleRole_failure_has_freshMiddleFanVariation
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hfailure : HasMiddleExtensionFailureWithRole χ polygon q .middle) :
    HasFreshMiddleFanVariation χ polygon q := by
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', _hj, hk, hk', hjq, hneq⟩ := hfailure
  subst j
  have memPolygon {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x ≠ q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hxq rfl).elim
    · exact hx
  exact ⟨i, i', k, k', hij, hi'j, hjk, hjk',
    memPolygon hi (by omega), memPolygon hi' (by omega),
    memPolygon hk (by omega), memPolygon hk' (by omega), hneq⟩

/-- A fresh right-endpoint failure needs no global after-polygon hypothesis:
it normalizes to an internal middle-word anomaly or the final boundary fan. -/
theorem rightEndpoint_failure_internal_or_final_without_order
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hfailure : HasMiddleExtensionFailureWithRole χ polygon q .rightEndpoint) :
    HasInternalRightEndpointMiddleAnomaly χ polygon hcard q ∨
      HasFinalMiddleFanVariation χ polygon hcard q := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (r : Fin 6) : e r ∈ polygon := polygon.orderEmbOfFin_mem hcard r
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
  have memPolygon {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x ≠ q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hxq rfl).elim
    · exact hx
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hrole, hneq⟩ := hfailure
  have hjq : j < q := by
    rcases hrole with rfl | rfl <;> omega
  have hiPolygon := memPolygon hi (by omega)
  have hi'Polygon := memPolygon hi' (by omega)
  have hjPolygon := memPolygon hj (by omega)
  have hfirst : e 0 < j := (firstLe hiPolygon).trans_lt hij
  have hlastLe : j ≤ e 5 := leLast hjPolygon
  by_cases hjLast : j = e 5
  · have hkq : k = q := by
      rcases Finset.mem_insert.mp hk with rfl | hkPolygon
      · rfl
      · exact (not_lt_of_ge (leLast hkPolygon) (hjLast ▸ hjk)).elim
    have hk'q : k' = q := by
      rcases Finset.mem_insert.mp hk' with rfl | hk'Polygon
      · rfl
      · exact (not_lt_of_ge (leLast hk'Polygon) (hjLast ▸ hjk')).elim
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
            simpa [hkq, hk'q] using (not_ne_iff.mp hfirstDiff).trans heq.symm
          exact Or.inl ⟨i', j, hi'j, hjq, hfirst, hlast,
            hi'Polygon, hjPolygon, hsecondDiff⟩
      · have hk'Polygon := memPolygon hk' hk'q
        have hpolygonEq :
            χ ⟨i', j, k', hi'j, hjk'⟩ =
              χ ⟨e 0, j, e 5, hfirst, hlast⟩ :=
          hmiddle hi'j hfirst hjk' hlast hi'Polygon (heMem 0)
            hjPolygon hk'Polygon (heMem 5)
        exact Or.inl ⟨i, j, hij, hjq, hfirst, hlast,
          hiPolygon, hjPolygon, by simpa [hkq, hpolygonEq] using hneq⟩
    · have hk'q : k' = q := hrole.resolve_left hkq
      have hkPolygon := memPolygon hk hkq
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

/-- Order-dually, a left-endpoint failure normalizes without requiring the
fresh vertex to precede the whole polygon: only the first boundary fan is
added to the internal middle-word anomaly. -/
theorem leftEndpoint_failure_internal_or_first_without_order
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)} {q : Fin n}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hfailure : HasMiddleExtensionFailureWithRole χ polygon q .leftEndpoint) :
    HasInternalLeftEndpointMiddleAnomaly χ polygon hcard q ∨
      HasFirstMiddleFanVariation χ polygon hcard q := by
  let e : Fin 6 ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (r : Fin 6) : e r ∈ polygon := polygon.orderEmbOfFin_mem hcard r
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
  have memPolygon {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x ≠ q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hxq rfl).elim
    · exact hx
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hrole, hneq⟩ := hfailure
  have hqj : q < j := by
    rcases hrole with rfl | rfl <;> omega
  have hjPolygon := memPolygon hj (by omega)
  have hkPolygon := memPolygon hk (by omega)
  have hk'Polygon := memPolygon hk' (by omega)
  have hfirstLe : e 0 ≤ j := firstLe hjPolygon
  have hlast : j < e 5 := hjk.trans_le (leLast hkPolygon)
  by_cases hjFirst : j = e 0
  · have hiq : i = q := by
      rcases Finset.mem_insert.mp hi with rfl | hiPolygon
      · rfl
      · have := firstLe hiPolygon
        omega
    have hi'q : i' = q := by
      rcases Finset.mem_insert.mp hi' with rfl | hi'Polygon
      · rfl
      · have := firstLe hi'Polygon
        omega
    exact Or.inr ⟨k, k', by simpa [hjFirst] using hqj,
      by simpa [hjFirst] using hjk, by simpa [hjFirst] using hjk',
      hkPolygon, hk'Polygon, by simpa [hjFirst, hiq, hi'q] using hneq⟩
  · have hfirst : e 0 < j := lt_of_le_of_ne hfirstLe (Ne.symm hjFirst)
    have hmiddle : IsMiddleDeterminedOn χ polygon :=
      FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
    by_cases hiq : i = q
    · by_cases hi'q : i' = q
      · by_cases hfirstDiff :
          χ ⟨q, j, k, hqj, hjk⟩ ≠ χ ⟨e 0, j, e 5, hfirst, hlast⟩
        · exact Or.inl ⟨j, k, hqj, hjk, hfirst, hlast,
            hjPolygon, hkPolygon, hfirstDiff⟩
        · have hsecondDiff :
              χ ⟨q, j, k', hqj, hjk'⟩ ≠
                χ ⟨e 0, j, e 5, hfirst, hlast⟩ := by
            intro heq
            apply hneq
            simpa [hiq, hi'q] using (not_ne_iff.mp hfirstDiff).trans heq.symm
          exact Or.inl ⟨j, k', hqj, hjk', hfirst, hlast,
            hjPolygon, hk'Polygon, hsecondDiff⟩
      · have hi'Polygon := memPolygon hi' hi'q
        have hpolygonEq :
            χ ⟨i', j, k', hi'j, hjk'⟩ =
              χ ⟨e 0, j, e 5, hfirst, hlast⟩ :=
          hmiddle hi'j hfirst hjk' hlast hi'Polygon (heMem 0)
            hjPolygon hk'Polygon (heMem 5)
        exact Or.inl ⟨j, k, hqj, hjk, hfirst, hlast,
          hjPolygon, hkPolygon, by simpa [hiq, hpolygonEq] using hneq⟩
    · have hi'q : i' = q := hrole.resolve_left hiq
      have hiPolygon := memPolygon hi hiq
      have hpolygonEq :
          χ ⟨i, j, k, hij, hjk⟩ =
            χ ⟨e 0, j, e 5, hfirst, hlast⟩ :=
        hmiddle hij hfirst hjk hlast hiPolygon (heMem 0)
          hjPolygon hkPolygon (heMem 5)
      exact Or.inl ⟨j, k', hqj, hjk', hfirst, hlast,
        hjPolygon, hk'Polygon, by
          intro heq
          apply hneq
          simpa [hi'q] using hpolygonEq.trans heq.symm⟩

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

/-- A localized right-endpoint failure against a crossing strong six is
either one triple disagreeing with the strong six's middle-word color, or a
genuine fan variation at that same internal middle. -/
theorem rightEndpoint_leftCore_internal_anomaly_or_fan
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)} {q : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hright : ∃ z ∈ polygon, z ∈ right)
    (hfailure : HasRightEndpointFailureWithLeftCore χ polygon left q) :
    HasInternalRightEndpointMiddleAnomaly χ polygon hcard q ∨
      HasInternalRightEndpointFanVariation χ polygon hcard q := by
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
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hrole, hiLeft, hi'Left, hjLeft, hneq⟩ := hfailure
  have hjq : j < q := by
    rcases hrole with rfl | rfl <;> omega
  have memPolygonOfLtQ {x : Fin n} (hx : x ∈ insert q polygon)
      (hxq : x < q) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (lt_irrefl _ hxq).elim
    · exact hx
  have hiPolygon := memPolygonOfLtQ hi (hij.trans hjq)
  have hi'Polygon := memPolygonOfLtQ hi' (hi'j.trans hjq)
  have hjPolygon := memPolygonOfLtQ hj hjq
  have hfirst : e 0 < j := (firstLe hiPolygon).trans_lt hij
  obtain ⟨z, hzPolygon, hzRight⟩ := hright
  have hlast : j < e 5 :=
    (horder j hjLeft z hzRight).trans_le (leLast hzPolygon)
  have hmiddle : IsMiddleDeterminedOn χ polygon :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
  by_cases hkq : k = q
  · by_cases hk'q : k' = q
    · exact Or.inr ⟨i, i', j, hij, hi'j, hjq, hfirst, hlast,
        hiPolygon, hi'Polygon, hjPolygon, by simpa [hkq, hk'q] using hneq⟩
    · have hk'Polygon : k' ∈ polygon := by
        rcases Finset.mem_insert.mp hk' with hk'q' | hk'Polygon
        · exact (hk'q hk'q').elim
        · exact hk'Polygon
      have hpolygonEq :
          χ ⟨i', j, k', hi'j, hjk'⟩ =
            χ ⟨e 0, j, e 5, hfirst, hlast⟩ :=
        hmiddle hi'j hfirst hjk' hlast hi'Polygon (heMem 0)
          hjPolygon hk'Polygon (heMem 5)
      exact Or.inl ⟨i, j, hij, hjq, hfirst, hlast, hiPolygon,
        hjPolygon, by simpa [hkq, hpolygonEq] using hneq⟩
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
    exact Or.inl ⟨i', j, hi'j, hjq, hfirst, hlast, hi'Polygon,
      hjPolygon, by
        intro heq
        apply hneq
        simpa [hk'q] using hpolygonEq.trans heq.symm⟩

/-- The order-dual normalization: a localized left-endpoint failure against
a crossing strong six is either a triple disagreeing with the middle-word
color, or a genuine fan variation at that internal middle. -/
theorem leftEndpoint_rightCore_internal_anomaly_or_fan
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)} {q : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hleft : ∃ z ∈ polygon, z ∈ left)
    (hfailure : HasLeftEndpointFailureWithRightCore χ polygon right q) :
    HasInternalLeftEndpointMiddleAnomaly χ polygon hcard q ∨
      HasInternalLeftEndpointFanVariation χ polygon hcard q := by
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
  obtain ⟨i, i', j, k, k', hij, hi'j, hjk, hjk',
    hi, hi', hj, hk, hk', hrole, hjRight, hkRight, hk'Right, hneq⟩ := hfailure
  have hqj : q < j := by
    rcases hrole with rfl | rfl <;> omega
  have memPolygonOfQLt {x : Fin n} (hx : x ∈ insert q polygon)
      (hqx : q < x) : x ∈ polygon := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (lt_irrefl _ hqx).elim
    · exact hx
  have hjPolygon := memPolygonOfQLt hj hqj
  have hkPolygon := memPolygonOfQLt hk (hqj.trans hjk)
  have hk'Polygon := memPolygonOfQLt hk' (hqj.trans hjk')
  obtain ⟨z, hzPolygon, hzLeft⟩ := hleft
  have hfirst : e 0 < j :=
    (firstLe hzPolygon).trans_lt (horder z hzLeft j hjRight)
  have hlast : j < e 5 := hjk.trans_le (leLast hkPolygon)
  have hmiddle : IsMiddleDeterminedOn χ polygon :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
  by_cases hiq : i = q
  · by_cases hi'q : i' = q
    · exact Or.inr ⟨j, k, k', hqj, hjk, hjk', hfirst, hlast,
        hjPolygon, hkPolygon, hk'Polygon, by simpa [hiq, hi'q] using hneq⟩
    · have hi'Polygon : i' ∈ polygon := by
        rcases Finset.mem_insert.mp hi' with hi'q' | hi'Polygon
        · exact (hi'q hi'q').elim
        · exact hi'Polygon
      have hpolygonEq :
          χ ⟨i', j, k', hi'j, hjk'⟩ =
            χ ⟨e 0, j, e 5, hfirst, hlast⟩ :=
        hmiddle hi'j hfirst hjk' hlast hi'Polygon (heMem 0)
          hjPolygon hk'Polygon (heMem 5)
      exact Or.inl ⟨j, k, hqj, hjk, hfirst, hlast, hjPolygon,
        hkPolygon, by simpa [hiq, hpolygonEq] using hneq⟩
  · have hi'q : i' = q := hrole.resolve_left hiq
    have hiPolygon : i ∈ polygon := by
      rcases Finset.mem_insert.mp hi with hiq' | hiPolygon
      · exact (hiq hiq').elim
      · exact hiPolygon
    have hpolygonEq :
        χ ⟨i, j, k, hij, hjk⟩ =
          χ ⟨e 0, j, e 5, hfirst, hlast⟩ :=
      hmiddle hij hfirst hjk hlast hiPolygon (heMem 0)
        hjPolygon hkPolygon (heMem 5)
    exact Or.inl ⟨j, k', hqj, hjk', hfirst, hlast, hjPolygon,
      hk'Polygon, by
        intro heq
        apply hneq
        simpa [hi'q] using hpolygonEq.trans heq.symm⟩

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

/-- The refined crossing-failure state whose extreme branches are anchored
to the strong six's middle-word color. The remaining endpoint and middle
roles are precisely the genuinely interleaving branches. -/
def HasCutMiddleWordReferencedFailure {n : ℕ} (χ : TripleColoring n)
    (left right polygon : Finset (Fin n)) (hcard : polygon.card = 6)
    (q : Fin n) : Prop :=
  (q ∈ left →
    HasMiddleExtensionFailureWithRole χ polygon q .leftEndpoint ∨
      HasMiddleExtensionFailureWithRole χ polygon q .middle ∨
      HasInternalRightEndpointMiddleAnomaly χ polygon hcard q ∨
      HasInternalRightEndpointFanVariation χ polygon hcard q) ∧
  (q ∈ right →
    HasInternalLeftEndpointMiddleAnomaly χ polygon hcard q ∨
      HasInternalLeftEndpointFanVariation χ polygon hcard q ∨
      HasMiddleExtensionFailureWithRole χ polygon q .middle ∨
      HasMiddleExtensionFailureWithRole χ polygon q .rightEndpoint)

/-- For a strong six crossing both sides, the localized extreme roles refine
to an anomaly against its middle word or an internal fan variation. -/
theorem cutLocalized_failure_refines_to_middleWordReferenced
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)} {q : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hleft : ∃ z ∈ polygon, z ∈ left)
    (hright : ∃ z ∈ polygon, z ∈ right)
    (hfailure : HasCutLocalizedMiddleFailure χ left right polygon q) :
    HasCutMiddleWordReferencedFailure χ left right polygon hcard q := by
  constructor
  · intro hqLeft
    rcases hfailure.1 hqLeft with hleftRole | hmiddle | hcore
    · exact Or.inl hleftRole
    · exact Or.inr (Or.inl hmiddle)
    · rcases rightEndpoint_leftCore_internal_anomaly_or_fan horder hcard
          hstrong hright hcore with hanomaly | hfan
      · exact Or.inr (Or.inr (Or.inl hanomaly))
      · exact Or.inr (Or.inr (Or.inr hfan))
  · intro hqRight
    rcases hfailure.2 hqRight with hcore | hmiddle | hrightRole
    · rcases leftEndpoint_rightCore_internal_anomaly_or_fan horder hcard
          hstrong hleft hcore with hanomaly | hfan
      · exact Or.inl hanomaly
      · exact Or.inr (Or.inl hfan)
    · exact Or.inr (Or.inr (Or.inl hmiddle))
    · exact Or.inr (Or.inr (Or.inr hrightRole))

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

/-- If both members of a mutually obstructed pair properly cross the cut,
all twelve directed failures are referenced to the appropriate polygon's
bounded middle word, except for the explicitly retained interleaving roles. -/
theorem mutuallyMiddleObstructedPair_has_middleWordReferenced_failures
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
    (∀ q ∈ second,
      HasCutMiddleWordReferencedFailure χ left right first hmutual.2.1 q) ∧
    (∀ q ∈ first,
      HasCutMiddleWordReferencedFailure χ left right second hmutual.2.2.1 q) := by
  have hlocalized := mutuallyMiddleObstructedPair_has_cutLocalized_failures
    horder hfirstSub hsecondSub hmutual
  constructor
  · intro q hqSecond
    exact cutLocalized_failure_refines_to_middleWordReferenced horder
      hmutual.2.1 hmutual.2.2.2.1 hfirstLeft hfirstRight
      (hlocalized.1 q hqSecond)
  · intro q hqFirst
    exact cutLocalized_failure_refines_to_middleWordReferenced horder
      hmutual.2.2.1 hmutual.2.2.2.2.1 hsecondLeft hsecondRight
      (hlocalized.2 q hqFirst)

/-- The final five-way local state for a failed extension by a vertex on
either side of the cut. Every branch is now an explicit anomaly or fan
variation; no bare extension-failure role remains. -/
def HasFullyNormalizedCutFailure {n : ℕ} (χ : TripleColoring n)
    (left right polygon : Finset (Fin n)) (hcard : polygon.card = 6)
    (q : Fin n) : Prop :=
  (q ∈ left →
    HasInternalLeftEndpointMiddleAnomaly χ polygon hcard q ∨
      HasFirstMiddleFanVariation χ polygon hcard q ∨
      HasFreshMiddleFanVariation χ polygon q ∨
      HasInternalRightEndpointMiddleAnomaly χ polygon hcard q ∨
      HasInternalRightEndpointFanVariation χ polygon hcard q) ∧
  (q ∈ right →
    HasInternalLeftEndpointMiddleAnomaly χ polygon hcard q ∨
      HasInternalLeftEndpointFanVariation χ polygon hcard q ∨
      HasFreshMiddleFanVariation χ polygon q ∨
      HasInternalRightEndpointMiddleAnomaly χ polygon hcard q ∨
      HasFinalMiddleFanVariation χ polygon hcard q)

/-- The middle-word-referenced state refines to the explicit five-way state
by normalizing its three remaining raw roles. -/
theorem middleWordReferenced_failure_refines_to_fullyNormalized
    {n : ℕ} {χ : TripleColoring n}
    {left right polygon : Finset (Fin n)} {q : Fin n}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hfailure : HasCutMiddleWordReferencedFailure χ left right polygon hcard q) :
    HasFullyNormalizedCutFailure χ left right polygon hcard q := by
  constructor
  · intro hqLeft
    rcases hfailure.1 hqLeft with hleftRole | hmiddle | hanomaly | hfan
    · rcases leftEndpoint_failure_internal_or_first_without_order hcard
          hstrong hleftRole with hanomaly | hfirstFan
      · exact Or.inl hanomaly
      · exact Or.inr (Or.inl hfirstFan)
    · exact Or.inr (Or.inr (Or.inl
        (middleRole_failure_has_freshMiddleFanVariation hmiddle)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hanomaly)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hfan)))
  · intro hqRight
    rcases hfailure.2 hqRight with hanomaly | hfan | hmiddle | hrightRole
    · exact Or.inl hanomaly
    · exact Or.inr (Or.inl hfan)
    · exact Or.inr (Or.inr (Or.inl
        (middleRole_failure_has_freshMiddleFanVariation hmiddle)))
    · rcases rightEndpoint_failure_internal_or_final_without_order hcard
          hstrong hrightRole with hanomaly | hfinalFan
      · exact Or.inr (Or.inr (Or.inr (Or.inl hanomaly)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hfinalFan)))

/-- All twelve failures of a properly crossing mutually obstructed pair have
the explicit five-way normalization in both directions. -/
theorem mutuallyMiddleObstructedPair_has_fullyNormalized_failures
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
    (∀ q ∈ second,
      HasFullyNormalizedCutFailure χ left right first hmutual.2.1 q) ∧
    (∀ q ∈ first,
      HasFullyNormalizedCutFailure χ left right second hmutual.2.2.1 q) := by
  have href := mutuallyMiddleObstructedPair_has_middleWordReferenced_failures
    horder hfirstSub hsecondSub hfirstLeft hfirstRight hsecondLeft
      hsecondRight hmutual
  constructor
  · intro q hqSecond
    exact middleWordReferenced_failure_refines_to_fullyNormalized hmutual.2.1
      hmutual.2.2.2.1 (href.1 q hqSecond)
  · intro q hqFirst
    exact middleWordReferenced_failure_refines_to_fullyNormalized hmutual.2.2.1
      hmutual.2.2.2.2.1 (href.2 q hqFirst)

/-- The five proper side splits of a strong six, packaged as a reusable state
predicate. -/
def HasProperStrongSixCrossingSplit {n : ℕ} (polygon left right : Finset (Fin n)) : Prop :=
  ((polygon ∩ left).card = 1 ∧ (polygon ∩ right).card = 5) ∨
  ((polygon ∩ left).card = 2 ∧ (polygon ∩ right).card = 4) ∨
  ((polygon ∩ left).card = 3 ∧ (polygon ∩ right).card = 3) ∨
  ((polygon ∩ left).card = 4 ∧ (polygon ∩ right).card = 2) ∨
  ((polygon ∩ left).card = 5 ∧ (polygon ∩ right).card = 1)

/-- Every proper crossing split supplies an actual polygon vertex on each
side, the hypotheses needed by the middle-word-referenced normalization. -/
theorem properStrongSixCrossingSplit_has_side_vertices
    {n : ℕ} {polygon left right : Finset (Fin n)}
    (hsplit : HasProperStrongSixCrossingSplit polygon left right) :
    (∃ z ∈ polygon, z ∈ left) ∧ (∃ z ∈ polygon, z ∈ right) := by
  have hpos : 0 < (polygon ∩ left).card ∧ 0 < (polygon ∩ right).card := by
    rcases hsplit with hsplit | hsplit | hsplit | hsplit | hsplit <;> omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos.1
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos.2
  exact ⟨⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩,
    ⟨y, (Finset.mem_inter.mp hy).1, (Finset.mem_inter.mp hy).2⟩⟩

/-- Complete local state of two mutually obstructed crossing strong sixes
under the ambient cap-five/cup-six exclusions: both words have weight one or
two, both splits are proper, and all twelve failures have the explicit
five-way anomaly/fan normalization. -/
theorem mutuallyMiddleObstructedPair_has_bounded_crossing_state
    {n : ℕ} {χ : TripleColoring n}
    {left right first second : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hfirstSub : first ⊆ left ∪ right)
    (hsecondSub : second ⊆ left ∪ right)
    (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second)
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hnoCapFive : ¬ContainsCapSet χ (left ∪ right) 5)
    (hnoCupSix : ¬ContainsCupSet χ (left ∪ right) 6) :
    StrongSixMiddleWordWeightOneOrTwo χ first hmutual.2.1 ∧
    StrongSixMiddleWordWeightOneOrTwo χ second hmutual.2.2.1 ∧
    HasProperStrongSixCrossingSplit first left right ∧
    HasProperStrongSixCrossingSplit second left right ∧
    ((∀ q ∈ second,
        HasFullyNormalizedCutFailure χ left right first hmutual.2.1 q) ∧
      (∀ q ∈ first,
        HasFullyNormalizedCutFailure χ left right second hmutual.2.2.1 q)) := by
  have hfirstSplit : HasProperStrongSixCrossingSplit first left right := by
    simpa only [HasProperStrongSixCrossingSplit] using
      strongSix_has_proper_crossing_split hdisjoint hfirstSub hmutual.2.1
        hmutual.2.2.2.1 hnoLeftStrong hnoRightStrong
  have hsecondSplit : HasProperStrongSixCrossingSplit second left right := by
    simpa only [HasProperStrongSixCrossingSplit] using
      strongSix_has_proper_crossing_split hdisjoint hsecondSub hmutual.2.2.1
        hmutual.2.2.2.2.1 hnoLeftStrong hnoRightStrong
  have hfirstNoCap : ¬ContainsCapSet χ first 5 := fun hcap ↦
    hnoCapFive (FinsetPolygon.ContainsCapSet.mono hcap hfirstSub)
  have hfirstNoCup : ¬ContainsCupSet χ first 6 := fun hcup ↦
    hnoCupSix (FinsetPolygon.ContainsCupSet.mono hcup hfirstSub)
  have hsecondNoCap : ¬ContainsCapSet χ second 5 := fun hcap ↦
    hnoCapFive (FinsetPolygon.ContainsCapSet.mono hcap hsecondSub)
  have hsecondNoCup : ¬ContainsCupSet χ second 6 := fun hcup ↦
    hnoCupSix (FinsetPolygon.ContainsCupSet.mono hcup hsecondSub)
  have hfirstWord := strongSix_middle_word_weight_one_or_two hmutual.2.1
    hmutual.2.2.2.1 hfirstNoCap hfirstNoCup
  have hsecondWord := strongSix_middle_word_weight_one_or_two hmutual.2.2.1
    hmutual.2.2.2.2.1 hsecondNoCap hsecondNoCup
  obtain ⟨hfirstLeft, hfirstRight⟩ :=
    properStrongSixCrossingSplit_has_side_vertices hfirstSplit
  obtain ⟨hsecondLeft, hsecondRight⟩ :=
    properStrongSixCrossingSplit_has_side_vertices hsecondSplit
  have hfailures :=
    mutuallyMiddleObstructedPair_has_fullyNormalized_failures horder
      hfirstSub hsecondSub hfirstLeft hfirstRight hsecondLeft hsecondRight
      hmutual
  exact ⟨hfirstWord, hsecondWord, hfirstSplit, hsecondSplit, hfailures⟩

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

/-- Packing now lands directly in the complete bounded crossing state: the
deleted strong six has a disjoint partner, both have proper crossing splits
and bounded middle words, and all twelve failures have an explicit five-way
anomaly/fan normalization. -/
theorem packedStrongSix_has_bounded_crossing_state_partner
    {n : ℕ} {χ : TripleColoring n} {left right first : Finset (Fin n)}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hfirstSub : first ⊆ left ∪ right) (hfirstCard : first.card = 6)
    (hfirstStrong : IsStrongPolygonSet χ first)
    (hpacking : StrongSixAvoidsEverySix χ (left ∪ right))
    (hnoLeftStrong : ¬ContainsStrongPolygonSet χ left 6)
    (hnoRightStrong : ¬ContainsStrongPolygonSet χ right 6)
    (hnoCapFive : ¬ContainsCapSet χ (left ∪ right) 5)
    (hnoCupSix : ¬ContainsCupSet χ (left ∪ right) 6)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    ∃ (second : Finset (Fin n)) (_hsecondSub : second ⊆ left ∪ right)
        (hmutual : MutuallyMiddleObstructedStrongSixPair χ first second),
      StrongSixMiddleWordWeightOneOrTwo χ first hmutual.2.1 ∧
      StrongSixMiddleWordWeightOneOrTwo χ second hmutual.2.2.1 ∧
      HasProperStrongSixCrossingSplit first left right ∧
      HasProperStrongSixCrossingSplit second left right ∧
      ((∀ q ∈ second,
          HasFullyNormalizedCutFailure χ left right first hmutual.2.1 q) ∧
        (∀ q ∈ first,
          HasFullyNormalizedCutFailure χ left right second hmutual.2.2.1 q)) := by
  obtain ⟨second, hsecondSub, hmutual, _hsplit⟩ :=
    packedStrongSix_has_mutuallyObstructed_split_partner hdisjoint hfirstSub
      hfirstCard hfirstStrong hpacking hnoLeftStrong hnoRightStrong
      hnoStrongSeven
  exact ⟨second, hsecondSub, hmutual,
    mutuallyMiddleObstructedPair_has_bounded_crossing_state hdisjoint horder
      hfirstSub hsecondSub hmutual hnoLeftStrong hnoRightStrong hnoCapFive
      hnoCupSix⟩

end ErdosSzekeres

end
