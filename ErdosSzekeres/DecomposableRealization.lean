module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Realizing recursive deep-below colorings

The parts of `HasDeepBelowSplit` may interleave in sweep order, so the
contiguous composition theorem from `Composition` does not apply directly.
This file keeps the prescribed abscissa `x_i = i` and recursively applies
opposite vertical shifts to the two child ordinate functions.  The resulting
construction proves that every abstract recursively decomposable coloring is
induced by a genuine planar sweep configuration.  The conclusion realizes the
coloring; it does not claim that the same recursive tree is witnessed by the
stronger coordinate predicate `IsGeometricallyDeepBelow`.
-/

namespace ErdosSzekeres

noncomputable section

/-- The point with prescribed ordinate and abscissa equal to its sweep index. -/
def ordinatePoint {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : Point 2 :=
  ![(i.val : ℝ), y i]

@[simp] theorem ordinatePoint_zero {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    ordinatePoint y i 0 = (i.val : ℝ) := by
  simp [ordinatePoint]

@[simp] theorem ordinatePoint_one {n : ℕ} (y : Fin n → ℝ) (i : Fin n) :
    ordinatePoint y i 1 = y i := by
  simp [ordinatePoint]

/-- Lower vertices receive level `-1`; all other vertices receive level `1`. -/
def splitLevel {n : ℕ} (lower : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ lower then -1 else 1

/-- Orientation is linear in a pointwise ordinate perturbation. -/
theorem orientation_ordinatePoint_add_smul {n : ℕ}
    (y z : Fin n → ℝ) (M : ℝ) (i j k : Fin n) :
    orientation (ordinatePoint (fun q => y q + M * z q) i)
        (ordinatePoint (fun q => y q + M * z q) j)
        (ordinatePoint (fun q => y q + M * z q) k) =
      orientation (ordinatePoint y i) (ordinatePoint y j) (ordinatePoint y k) +
        M * orientation (ordinatePoint z i) (ordinatePoint z j)
          (ordinatePoint z k) := by
  simp [orientation, ordinatePoint]
  ring

/-- On a crossing triple whose middle vertex is lower, the split-level
perturbation has positive orientation. -/
theorem orientation_splitLevel_pos_of_middle_lower {n : ℕ}
    {lower upper : Finset (Fin n)} (hdisjoint : Disjoint lower upper)
    (t : OrderedTriple n)
    (hi : t.i ∈ lower ∪ upper) (hj : t.j ∈ lower)
    (hk : t.k ∈ lower ∪ upper)
    (hcrossLower : ¬(t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower)) :
    0 < orientation (ordinatePoint (splitLevel lower) t.i)
      (ordinatePoint (splitLevel lower) t.j)
      (ordinatePoint (splitLevel lower) t.k) := by
  have hdisj := Finset.disjoint_left.mp hdisjoint
  have hijR : (t.i.val : ℝ) < t.j.val := by exact_mod_cast t.hij
  have hjkR : (t.j.val : ℝ) < t.k.val := by exact_mod_cast t.hjk
  have hikR : (t.i.val : ℝ) < t.k.val := hijR.trans hjkR
  rcases Finset.mem_union.mp hi with hiL | hiU <;>
    rcases Finset.mem_union.mp hk with hkL | hkU
  · exact (hcrossLower ⟨hiL, hj, hkL⟩).elim
  · have hkNotL : t.k ∉ lower := fun hkL => hdisj hkL hkU
    simpa [orientation, ordinatePoint, splitLevel, hiL, hj, hkNotL] using hijR
  · have hiNotL : t.i ∉ lower := fun hiL => hdisj hiL hiU
    simp [orientation, ordinatePoint, splitLevel, hiNotL, hj, hkL]
    nlinarith [hjkR]
  · have hiNotL : t.i ∉ lower := fun hiL => hdisj hiL hiU
    have hkNotL : t.k ∉ lower := fun hkL => hdisj hkL hkU
    simp [orientation, ordinatePoint, splitLevel, hiNotL, hj, hkNotL]
    nlinarith [hikR]

/-- On a crossing triple whose middle vertex is upper, the split-level
perturbation has negative orientation. -/
theorem orientation_splitLevel_neg_of_middle_upper {n : ℕ}
    {lower upper : Finset (Fin n)} (hdisjoint : Disjoint lower upper)
    (t : OrderedTriple n)
    (hi : t.i ∈ lower ∪ upper) (hj : t.j ∈ upper)
    (hk : t.k ∈ lower ∪ upper)
    (hcrossUpper : ¬(t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper)) :
    orientation (ordinatePoint (splitLevel lower) t.i)
      (ordinatePoint (splitLevel lower) t.j)
      (ordinatePoint (splitLevel lower) t.k) < 0 := by
  have hdisj := Finset.disjoint_left.mp hdisjoint
  have hjNotL : t.j ∉ lower := fun hjL => hdisj hjL hj
  have hijR : (t.i.val : ℝ) < t.j.val := by exact_mod_cast t.hij
  have hjkR : (t.j.val : ℝ) < t.k.val := by exact_mod_cast t.hjk
  have hikR : (t.i.val : ℝ) < t.k.val := hijR.trans hjkR
  rcases Finset.mem_union.mp hi with hiL | hiU <;>
    rcases Finset.mem_union.mp hk with hkL | hkU
  · simpa [orientation, ordinatePoint, splitLevel, hiL, hjNotL, hkL] using hikR
  · have hkNotL : t.k ∉ lower := fun hkL => hdisj hkL hkU
    simp [orientation, ordinatePoint, splitLevel, hiL, hjNotL, hkNotL]
    nlinarith [hjkR]
  · have hiNotL : t.i ∉ lower := fun hiL => hdisj hiL hiU
    simp [orientation, ordinatePoint, splitLevel, hiNotL, hjNotL, hkL]
    nlinarith [hijR]
  · exact (hcrossUpper ⟨hiU, hj, hkU⟩).elim

/-- Strict orientation sign corresponding to a left or right turn. -/
def RealizesTurn (c : Turn) (x : ℝ) : Prop :=
  match c with
  | .left => 0 < x
  | .right => x < 0

/-- An ordinate function realizes `χ` on `s` with the fixed abscissae
`x_i = i`.  No condition is imposed on triples using vertices outside `s`. -/
def FixedXRealizesOn {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) (y : Fin n → ℝ) : Prop :=
  ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s →
    RealizesTurn (χ t)
      (orientation (ordinatePoint y t.i) (ordinatePoint y t.j)
        (ordinatePoint y t.k))

/-- Piece together the two child ordinate functions before separating them. -/
def splitBase {n : ℕ} (lower : Finset (Fin n))
    (yLower yUpper : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i ∈ lower then yLower i else yUpper i

/-- The vertical shift threshold for one potential triple.  On a crossing
triple its denominator has the desired strict sign. -/
def splitThreshold {n : ℕ} (lower : Finset (Fin n))
    (base : Fin n → ℝ) (q : (Fin n × Fin n) × Fin n) : ℝ :=
  let O := orientation (ordinatePoint base q.1.1)
    (ordinatePoint base q.1.2) (ordinatePoint base q.2)
  let C := orientation (ordinatePoint (splitLevel lower) q.1.1)
    (ordinatePoint (splitLevel lower) q.1.2)
      (ordinatePoint (splitLevel lower) q.2)
  if q.1.2 ∈ lower then -O / C else O / (-C)

/-- Two fixed-abscissa child realizations can be shifted while preserving both
internal colorings and realizing every crossing color of an arbitrary,
possibly interleaved, abstract deep-below split. -/
theorem FixedXRealizesOn.deepBelowMerge {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)} {yLower yUpper : Fin n → ℝ}
    (hLower : FixedXRealizesOn χ lower yLower)
    (hUpper : FixedXRealizesOn χ upper yUpper)
    (hdeep : HasDeepBelowSplit χ lower upper) :
    ∃ M : ℝ, FixedXRealizesOn χ (lower ∪ upper)
      (fun i => splitBase lower yLower yUpper i + M * splitLevel lower i) := by
  let base := splitBase lower yLower yUpper
  obtain ⟨bound, hbound⟩ := exists_strictUpperBound_of_finite
    (splitThreshold lower base)
  let M := max bound 0
  refine ⟨M, ?_⟩
  intro t hi hj hk
  by_cases hallLower : t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower
  · have h := hLower t hallLower.1 hallLower.2.1 hallLower.2.2
    simpa [base, splitBase, splitLevel, hallLower.1, hallLower.2.1,
      hallLower.2.2, orientation, ordinatePoint] using h
  by_cases hallUpper : t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper
  · have hdisj := Finset.disjoint_left.mp hdeep.disjoint
    have hiNotL : t.i ∉ lower := fun hiL => hdisj hiL hallUpper.1
    have hjNotL : t.j ∉ lower := fun hjL => hdisj hjL hallUpper.2.1
    have hkNotL : t.k ∉ lower := fun hkL => hdisj hkL hallUpper.2.2
    have h := hUpper t hallUpper.1 hallUpper.2.1 hallUpper.2.2
    simpa [base, splitBase, splitLevel, hiNotL, hjNotL, hkNotL,
      orientation, ordinatePoint] using h
  have hcolor := hdeep.crossing t hi hj hk hallLower hallUpper
  have hM : splitThreshold lower base ((t.i, t.j), t.k) < M :=
    (hbound ((t.i, t.j), t.k)).trans_le (le_max_left bound 0)
  by_cases hjLower : t.j ∈ lower
  · have hC := orientation_splitLevel_pos_of_middle_lower hdeep.disjoint t
      hi hjLower hk hallLower
    rw [hcolor, if_pos hjLower]
    simp only [RealizesTurn]
    rw [orientation_ordinatePoint_add_smul]
    have hratio :
        -orientation (ordinatePoint base t.i) (ordinatePoint base t.j)
              (ordinatePoint base t.k) /
            orientation (ordinatePoint (splitLevel lower) t.i)
              (ordinatePoint (splitLevel lower) t.j)
              (ordinatePoint (splitLevel lower) t.k) < M := by
      simpa [splitThreshold, hjLower] using hM
    have := (div_lt_iff₀ hC).mp hratio
    nlinarith
  · have hjUpper : t.j ∈ upper :=
      (Finset.mem_union.mp hj).resolve_left hjLower
    have hC := orientation_splitLevel_neg_of_middle_upper hdeep.disjoint t
      hi hjUpper hk hallUpper
    rw [hcolor, if_neg hjLower]
    simp only [RealizesTurn]
    rw [orientation_ordinatePoint_add_smul]
    have hnegC : 0 < -orientation (ordinatePoint (splitLevel lower) t.i)
        (ordinatePoint (splitLevel lower) t.j)
        (ordinatePoint (splitLevel lower) t.k) := by linarith
    have hratio :
        orientation (ordinatePoint base t.i) (ordinatePoint base t.j)
              (ordinatePoint base t.k) /
            (-orientation (ordinatePoint (splitLevel lower) t.i)
              (ordinatePoint (splitLevel lower) t.j)
              (ordinatePoint (splitLevel lower) t.k)) < M := by
      simpa [splitThreshold, hjLower] using hM
    have := (div_lt_iff₀ hnegC).mp hratio
    nlinarith

/-- A singleton is vacuously realized by the zero ordinate function. -/
theorem FixedXRealizesOn.singleton {n : ℕ} (χ : TripleColoring n)
    (i : Fin n) : FixedXRealizesOn χ {i} (fun _ => 0) := by
  intro t hi hj _
  simp only [Finset.mem_singleton] at hi hj
  have hij : t.i = t.j := hi.trans hj.symm
  exact (ne_of_lt t.hij hij).elim

/-- Recursive deep-below decomposability supplies a fixed-abscissa ordinate
realization on the complete decomposed subset. -/
theorem IsDecomposableOn.exists_fixedXRealization {n : ℕ}
    {χ : TripleColoring n} {s : Finset (Fin n)}
    (h : IsDecomposableOn χ s) :
    ∃ y : Fin n → ℝ, FixedXRealizesOn χ s y := by
  induction h with
  | singleton i => exact ⟨fun _ => 0, FixedXRealizesOn.singleton χ i⟩
  | @split lower upper hLower hUpper hdeep ihLower ihUpper =>
      obtain ⟨yLower, hyLower⟩ := ihLower
      obtain ⟨yUpper, hyUpper⟩ := ihUpper
      obtain ⟨M, hM⟩ := hyLower.deepBelowMerge hyUpper hdeep
      exact ⟨fun i => splitBase lower yLower yUpper i + M * splitLevel lower i, hM⟩

/-- A realization on all indices gives a genuine swept configuration with
the prescribed points and triple coloring. -/
theorem FixedXRealizesOn.exists_sweptConfiguration {n : ℕ}
    {χ : TripleColoring n} {y : Fin n → ℝ}
    (h : FixedXRealizesOn χ Finset.univ y) :
    ∃ P : SweptConfiguration n, P.point = ordinatePoint y ∧
      P.tripleColoring = χ := by
  let P : SweptConfiguration n :=
    { point := ordinatePoint y
      sweep_strictMono := by
        intro i j hij
        simp only [ordinatePoint_zero]
        exact_mod_cast hij
      generalPosition := by
        apply generalPosition_of_ordered
        intro i j k hij hjk
        let t : OrderedTriple n := ⟨i, j, k, hij, hjk⟩
        have ht := h t (by simp) (by simp) (by simp)
        cases hc : χ t <;> rw [hc] at ht <;>
          simp only [RealizesTurn] at ht <;> linarith }
  refine ⟨P, rfl, ?_⟩
  funext t
  have ht := h t (by simp) (by simp) (by simp)
  cases hc : χ t
  · change P.turn t.i t.j t.k = Turn.left
    apply (P.turn_eq_left_iff t.i t.j t.k).2
    simpa [P, RealizesTurn, hc] using ht
  · change P.turn t.i t.j t.k = Turn.right
    apply (P.turn_eq_right_iff t.i t.j t.k t.hij t.hjk).2
    simpa [P, RealizesTurn, hc] using ht

/-- Every abstract recursively decomposable coloring is sweep-realizable by
an actual planar point configuration in general position. -/
theorem IsDecomposable.isSweepRealizable {n : ℕ} {χ : TripleColoring n}
    (h : IsDecomposable χ) : IsSweepRealizable χ := by
  obtain ⟨y, hy⟩ := h.exists_fixedXRealization
  obtain ⟨P, _, hP⟩ := hy.exists_sweptConfiguration
  exact ⟨P, hP⟩

end

end ErdosSzekeres

end
