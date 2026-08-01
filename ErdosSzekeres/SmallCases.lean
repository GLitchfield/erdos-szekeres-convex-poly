import ErdosSzekeres.CupCap

/-!
# Exact small cases of the Erdős--Szekeres formula

The three-point case follows from Carathéodory's four-subset criterion.  For
four points, we prove the rank-three signotope law directly from orientation
inequalities, exhaust its five overlapping four-tuples on five vertices, and
transport the resulting strong polygon back to the public geometric API.
Explicit sharpness configurations complete the exact cases `n = 3` and
`n = 4`.  The substantially deeper nine-point proof for `n = 5` remains a
separate milestone.
-/

namespace ErdosSzekeres

noncomputable section

theorem inConvexPosition_of_card_le_three {s : Finset (Point 2)}
    (hgp : InGeneralPosition s) (hcard : s.card ≤ 3) : InConvexPosition s := by
  apply (inConvexPosition_iff_four_subsets s hgp).2
  intro t hts htcard
  have := Finset.card_le_card hts
  omega

theorem forces_three : ForcesConvexPolygon 3 3 := by
  intro s hcard hgp
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨t, hts, htcard, inConvexPosition_of_card_le_three
    (hgp.mono hts) (by omega)⟩

def sharpnessThreePoint0 : Point 2 := ![0, 0]
def sharpnessThreePoint1 : Point 2 := ![1, 0]
def sharpnessThreeSet : Finset (Point 2) :=
  {sharpnessThreePoint0, sharpnessThreePoint1}

theorem sharpnessThreePoint_ne : sharpnessThreePoint0 ≠ sharpnessThreePoint1 := by
  intro h
  have := congrFun h 0
  norm_num [sharpnessThreePoint0, sharpnessThreePoint1] at this

@[simp] theorem card_sharpnessThreeSet : sharpnessThreeSet.card = 2 := by
  simp [sharpnessThreeSet, sharpnessThreePoint_ne]

theorem sharpnessThreeSet_generalPosition :
    InGeneralPosition sharpnessThreeSet := by
  intro a ha b hb c hc hab hac hbc
  simp only [sharpnessThreeSet, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
      rcases hc with rfl | rfl <;> simp_all

theorem sharpness_three : HasSharpnessExample 3 3 := by
  refine ⟨sharpnessThreeSet, by simp, sharpnessThreeSet_generalPosition, ?_⟩
  rintro ⟨t, hts, htcard, _⟩
  have hle := Finset.card_le_card hts
  simp at hle
  omega

theorem erdosSzekeresFormulaAt_three : ErdosSzekeresFormulaAt 3 := by
  norm_num [ErdosSzekeresFormulaAt]
  exact ⟨forces_three, sharpness_three⟩

def TurnSequenceAllowed (a b c d : Turn) : Prop :=
  (a = Turn.left ∧ b = Turn.left ∧ c = Turn.left ∧ d = Turn.left) ∨
  (a = Turn.left ∧ b = Turn.left ∧ c = Turn.left ∧ d = Turn.right) ∨
  (a = Turn.left ∧ b = Turn.left ∧ c = Turn.right ∧ d = Turn.right) ∨
  (a = Turn.left ∧ b = Turn.right ∧ c = Turn.right ∧ d = Turn.right) ∨
  (a = Turn.right ∧ b = Turn.right ∧ c = Turn.right ∧ d = Turn.right) ∨
  (a = Turn.right ∧ b = Turn.right ∧ c = Turn.right ∧ d = Turn.left) ∨
  (a = Turn.right ∧ b = Turn.right ∧ c = Turn.left ∧ d = Turn.left) ∨
  (a = Turn.right ∧ b = Turn.left ∧ c = Turn.left ∧ d = Turn.left)

theorem SweptConfiguration.turnSequenceAllowed {n : ℕ}
    (P : SweptConfiguration n) (i j k l : Fin n)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    TurnSequenceAllowed (P.turn i j k) (P.turn i j l)
      (P.turn i k l) (P.turn j k l) := by
  have hxij := P.sweep_strictMono hij
  have hxjk := P.sweep_strictMono hjk
  have hxkl := P.sweep_strictMono hkl
  have hijk := P.generalPosition (ne_of_lt hij)
    (ne_of_lt (hij.trans hjk)) (ne_of_lt hjk)
  have hijl := P.generalPosition (ne_of_lt hij)
    (ne_of_lt (hij.trans (hjk.trans hkl))) (ne_of_lt (hjk.trans hkl))
  have hikl := P.generalPosition (ne_of_lt (hij.trans hjk))
    (ne_of_lt ((hij.trans hjk).trans hkl)) (ne_of_lt hkl)
  have hjkl := P.generalPosition (ne_of_lt hjk)
    (ne_of_lt (hjk.trans hkl)) (ne_of_lt hkl)
  by_cases h₁ : 0 < orientation (P.point i) (P.point j) (P.point k) <;>
    by_cases h₂ : 0 < orientation (P.point i) (P.point j) (P.point l) <;>
      by_cases h₃ : 0 < orientation (P.point i) (P.point k) (P.point l) <;>
        by_cases h₄ : 0 < orientation (P.point j) (P.point k) (P.point l) <;>
          simp [TurnSequenceAllowed, SweptConfiguration.turn, h₁, h₂, h₃, h₄] <;>
          simp only [orientation] at * <;> nlinarith

theorem five_turns_contain_strong_four
    (a b c d e f g h i j : Turn)
    (h₀ : TurnSequenceAllowed a b d g)
    (h₁ : TurnSequenceAllowed a c e h)
    (h₂ : TurnSequenceAllowed b c f i)
    (h₃ : TurnSequenceAllowed d e f j)
    (h₄ : TurnSequenceAllowed g h i j) :
    (a = b ∧ d = g) ∨ (a = c ∧ e = h) ∨
    (b = c ∧ f = i) ∨ (d = e ∧ f = j) ∨
    (g = h ∧ i = j) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
    cases f <;> cases g <;> cases h <;> cases i <;> cases j <;>
      simp_all [TurnSequenceAllowed]

def embedding0123 : Fin 4 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 3] (by decide)

def embedding0124 : Fin 4 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono ![0, 1, 2, 4] (by decide)

def embedding0134 : Fin 4 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono ![0, 1, 3, 4] (by decide)

def embedding0234 : Fin 4 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono ![0, 2, 3, 4] (by decide)

def embedding1234 : Fin 4 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono ![1, 2, 3, 4] (by decide)

theorem isStrongPolygonOn_finFour_iff {n : ℕ} (χ : TripleColoring n)
    (f : Fin 4 ↪o Fin n) :
    IsStrongPolygonOn χ f ↔
      χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩ =
        χ ⟨f 0, f 1, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩ ∧
      χ ⟨f 0, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩ =
        χ ⟨f 1, f 2, f 3, f.strictMono (by decide), f.strictMono (by decide)⟩ := by
  constructor
  · intro h
    exact h (by decide) (by decide) (by decide)
  · intro h i j k l hij hjk hkl
    have hi : i = 0 := by ext; omega
    have hj : j = 1 := by ext; omega
    have hk : k = 2 := by ext; omega
    have hl : l = 3 := by ext; omega
    subst i; subst j; subst k; subst l
    exact h

theorem SweptConfiguration.exists_strong_four (P : SweptConfiguration 5) :
    ∃ f : Fin 4 ↪o Fin 5, IsStrongPolygonOn P.tripleColoring f := by
  have h := five_turns_contain_strong_four
    (P.turn 0 1 2) (P.turn 0 1 3) (P.turn 0 1 4)
    (P.turn 0 2 3) (P.turn 0 2 4) (P.turn 0 3 4)
    (P.turn 1 2 3) (P.turn 1 2 4) (P.turn 1 3 4)
    (P.turn 2 3 4)
    (P.turnSequenceAllowed 0 1 2 3 (by decide) (by decide) (by decide))
    (P.turnSequenceAllowed 0 1 2 4 (by decide) (by decide) (by decide))
    (P.turnSequenceAllowed 0 1 3 4 (by decide) (by decide) (by decide))
    (P.turnSequenceAllowed 0 2 3 4 (by decide) (by decide) (by decide))
    (P.turnSequenceAllowed 1 2 3 4 (by decide) (by decide) (by decide))
  rcases h with h | h | h | h | h
  · refine ⟨embedding0123, (isStrongPolygonOn_finFour_iff
      P.tripleColoring embedding0123).2 ?_⟩
    simpa [embedding0123, SweptConfiguration.tripleColoring] using h
  · refine ⟨embedding0124, (isStrongPolygonOn_finFour_iff
      P.tripleColoring embedding0124).2 ?_⟩
    simpa [embedding0124, SweptConfiguration.tripleColoring] using h
  · refine ⟨embedding0134, (isStrongPolygonOn_finFour_iff
      P.tripleColoring embedding0134).2 ?_⟩
    simpa [embedding0134, SweptConfiguration.tripleColoring] using h
  · refine ⟨embedding0234, (isStrongPolygonOn_finFour_iff
      P.tripleColoring embedding0234).2 ?_⟩
    simpa [embedding0234, SweptConfiguration.tripleColoring] using h
  · refine ⟨embedding1234, (isStrongPolygonOn_finFour_iff
      P.tripleColoring embedding1234).2 ?_⟩
    simpa [embedding1234, SweptConfiguration.tripleColoring] using h

theorem SweptConfiguration.exists_strong_four_of_five_le
    {n : ℕ} (P : SweptConfiguration n) (hn : 5 ≤ n) :
    ∃ f : Fin 4 ↪o Fin n, IsStrongPolygonOn P.tripleColoring f := by
  let e : Fin 5 ↪o Fin n := Finset.univ.orderEmbOfCardLe (by simpa using hn)
  obtain ⟨f, hf⟩ := (P.restrict e).exists_strong_four
  let g : Fin 4 ↪o Fin n := f.trans e
  refine ⟨g, ?_⟩
  intro i j k l hij hjk hkl
  exact hf hij hjk hkl

theorem forces_four : ForcesConvexPolygon 4 5 := by
  intro s hcard hgp
  let P := Classical.choice (exists_sweptPresentation s hgp)
  obtain ⟨f, hf⟩ := P.configuration.exists_strong_four_of_five_le hcard
  exact (P.containsConvexSubset_iff_exists_isStrongPolygonOn 4).2 ⟨f, hf⟩

def sharpnessFourPoint0 : Point 2 := ![0, 0]
def sharpnessFourPoint1 : Point 2 := ![2, 0]
def sharpnessFourPoint2 : Point 2 := ![0, 2]
def sharpnessFourPoint3 : Point 2 := ![(1 : ℝ) / 2, (1 : ℝ) / 2]
def sharpnessFourSet : Finset (Point 2) :=
  {sharpnessFourPoint0, sharpnessFourPoint1,
    sharpnessFourPoint2, sharpnessFourPoint3}

@[simp] theorem card_sharpnessFourSet : sharpnessFourSet.card = 4 := by
  norm_num [sharpnessFourSet, sharpnessFourPoint0, sharpnessFourPoint1,
    sharpnessFourPoint2, sharpnessFourPoint3, Matrix.cons_val_zero,
    Matrix.cons_val_one]

theorem sharpnessFourSet_generalPosition :
    InGeneralPosition sharpnessFourSet := by
  intro a ha b hb c hc hab hac hbc
  simp only [sharpnessFourSet, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp_all [orientation, sharpnessFourPoint0, sharpnessFourPoint1,
          sharpnessFourPoint2, sharpnessFourPoint3] <;> norm_num

theorem not_inConvexPosition_sharpnessFourSet :
    ¬InConvexPosition sharpnessFourSet := by
  intro hconvex
  apply hconvex sharpnessFourPoint3 (by simp [sharpnessFourSet])
  have horient : 0 < orientation sharpnessFourPoint0 sharpnessFourPoint1
      sharpnessFourPoint2 := by
    norm_num [orientation, sharpnessFourPoint0, sharpnessFourPoint1,
      sharpnessFourPoint2]
  have hmem : sharpnessFourPoint3 ∈ convexHull ℝ
      (triangle sharpnessFourPoint0 sharpnessFourPoint1 sharpnessFourPoint2) := by
    rw [mem_convexHull_triangle_iff_of_orientation_pos _ _ _ _ horient]
    norm_num [leftClosedHalfPlane, orientation, sharpnessFourPoint0,
      sharpnessFourPoint1, sharpnessFourPoint2, sharpnessFourPoint3]
  have h₃₀ : sharpnessFourPoint3 ≠ sharpnessFourPoint0 := by
    intro h
    have := congrFun h 0
    norm_num [sharpnessFourPoint3, sharpnessFourPoint0] at this
  have h₃₁ : sharpnessFourPoint3 ≠ sharpnessFourPoint1 := by
    intro h
    have := congrFun h 0
    norm_num [sharpnessFourPoint3, sharpnessFourPoint1] at this
  have h₃₂ : sharpnessFourPoint3 ≠ sharpnessFourPoint2 := by
    intro h
    have := congrFun h 1
    norm_num [sharpnessFourPoint3, sharpnessFourPoint2] at this
  have herase : sharpnessFourSet.erase sharpnessFourPoint3 =
      {sharpnessFourPoint0, sharpnessFourPoint1, sharpnessFourPoint2} := by
    ext p
    simp only [sharpnessFourSet, Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hp, h | h | h | h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact (hp h).elim
    · rintro (h | h | h)
      · refine ⟨?_, Or.inl h⟩
        rintro rfl
        exact h₃₀ h
      · refine ⟨?_, Or.inr (Or.inl h)⟩
        rintro rfl
        exact h₃₁ h
      · refine ⟨?_, Or.inr (Or.inr (Or.inl h))⟩
        rintro rfl
        exact h₃₂ h
  rw [herase]
  simpa [triangle] using hmem

theorem sharpness_four : HasSharpnessExample 4 5 := by
  refine ⟨sharpnessFourSet, by simp, sharpnessFourSet_generalPosition, ?_⟩
  rintro ⟨t, hts, htcard, htconvex⟩
  have hts_eq : t = sharpnessFourSet :=
    Finset.eq_of_subset_of_card_le hts (by simp [htcard])
  exact not_inConvexPosition_sharpnessFourSet (hts_eq ▸ htconvex)

theorem erdosSzekeresFormulaAt_four : ErdosSzekeresFormulaAt 4 := by
  norm_num [ErdosSzekeresFormulaAt]
  exact ⟨forces_four, sharpness_four⟩


end

end ErdosSzekeres
