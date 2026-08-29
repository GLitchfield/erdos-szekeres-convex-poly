module

public import ErdosSzekeres.DecomposableRealization
public import ErdosSzekeres.MongeSubmodular

@[expose] public section

/-!
# A realizable strict local minimum for the crossing-mismatch energy

This file formalizes one fixed eight-point configuration. Its crossing-mismatch energy is two at
the frozen extreme-anchor labeling and is strictly larger at every free one-bit neighbor.
-/

namespace ErdosSzekeres
namespace CrossingMismatch

noncomputable section

/-- The exact ordinate vector `[-3,-3,-2,0,-2,-6,-8,5]`. -/
def mongeN8Heights : Fin 8 → ℝ :=
  ![-3, -3, -2, 0, -2, -6, -8, 5]

/-- The same ordinate vector over the integers, used only for finite turn computation. -/
def mongeN8IntHeights : Fin 8 → ℤ :=
  ![-3, -3, -2, 0, -2, -6, -8, 5]

/-- All ordered determinants of the frozen fixed-x points are nonzero. -/
theorem mongeN8_generalPosition :
    ∀ i j k : Fin 8, i < j → j < k →
      orientation (ordinatePoint mongeN8Heights i)
        (ordinatePoint mongeN8Heights j) (ordinatePoint mongeN8Heights k) ≠ 0 := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [mongeN8Heights, ordinatePoint, orientation]

/-- The exact fixed-x geometric realization of the eight-point witness. -/
def mongeN8Configuration : SweptConfiguration 8 where
  point := ordinatePoint mongeN8Heights
  sweep_strictMono := by
    intro i j hij
    simp only [ordinatePoint_zero]
    exact_mod_cast hij
  generalPosition := generalPosition_of_ordered _ mongeN8_generalPosition

/-- The coloring induced by the exact swept configuration. -/
def mongeN8Coloring : TripleColoring 8 :=
  mongeN8Configuration.tripleColoring

/-- The exact integer determinant for an increasing triple. -/
def mongeN8Det (t : OrderedTriple 8) : ℤ :=
  ((t.j.val : ℤ) - t.i.val) * (mongeN8IntHeights t.k - mongeN8IntHeights t.i) -
    (mongeN8IntHeights t.j - mongeN8IntHeights t.i) * ((t.k.val : ℤ) - t.i.val)

/-- The determinant-sign turn on any three indices. -/
def mongeN8Turn (i j k : Fin 8) : Turn :=
  let det := ((j.val : ℤ) - i.val) * (mongeN8IntHeights k - mongeN8IntHeights i) -
    (mongeN8IntHeights j - mongeN8IntHeights i) * ((k.val : ℤ) - i.val)
  if 0 < det then Turn.left else Turn.right

/-- A computable turn table obtained from the exact integer determinants. -/
def mongeN8TableColoring : TripleColoring 8 :=
  fun t ↦ mongeN8Turn t.i t.j t.k

/-- The computable turn table is exactly the coloring induced by the geometric configuration. -/
theorem mongeN8Coloring_eq_table : mongeN8Coloring = mongeN8TableColoring := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [mongeN8Coloring, mongeN8Configuration, mongeN8TableColoring,
    mongeN8Turn, mongeN8IntHeights, mongeN8Heights, SweptConfiguration.tripleColoring,
    SweptConfiguration.turn, ordinatePoint, orientation]

/-- The frozen labeling: vertices `0` through `6` are lower and vertex `7` is upper. -/
def mongeN8BaseLabel : Fin 8 → Bool :=
  ![false, false, false, false, false, false, false, true]

/-- Flip exactly one Boolean label. -/
def flipLabel {n : ℕ} (label : Fin n → Bool) (v : Fin n) (i : Fin n) : Bool :=
  if i = v then !(label i) else label i

/-- The base labeling with free vertex `1` flipped. -/
def mongeN8Flip1 : Fin 8 → Bool := flipLabel mongeN8BaseLabel 1

/-- The base labeling with free vertex `2` flipped. -/
def mongeN8Flip2 : Fin 8 → Bool := flipLabel mongeN8BaseLabel 2

/-- The base labeling with free vertex `3` flipped. -/
def mongeN8Flip3 : Fin 8 → Bool := flipLabel mongeN8BaseLabel 3

/-- The base labeling with free vertex `4` flipped. -/
def mongeN8Flip4 : Fin 8 → Bool := flipLabel mongeN8BaseLabel 4

/-- The base labeling with free vertex `5` flipped. -/
def mongeN8Flip5 : Fin 8 → Bool := flipLabel mongeN8BaseLabel 5

/-- The base labeling with free vertex `6` flipped. -/
def mongeN8Flip6 : Fin 8 → Bool := flipLabel mongeN8BaseLabel 6

/-- The ten strong-polygon equalities on five increasing vertex values. -/
def mongeN8StrongFiveLaws (a b c d e : Fin 8) : Prop :=
  mongeN8Turn a b c = mongeN8Turn a b d ∧
  mongeN8Turn a c d = mongeN8Turn b c d ∧
  mongeN8Turn a b c = mongeN8Turn a b e ∧
  mongeN8Turn a c e = mongeN8Turn b c e ∧
  mongeN8Turn a b d = mongeN8Turn a b e ∧
  mongeN8Turn a d e = mongeN8Turn b d e ∧
  mongeN8Turn a c d = mongeN8Turn a c e ∧
  mongeN8Turn a d e = mongeN8Turn c d e ∧
  mongeN8Turn b c d = mongeN8Turn b c e ∧
  mongeN8Turn b d e = mongeN8Turn c d e

/-- The ten finite turn equalities are decidable. -/
instance mongeN8StrongFiveLawsDecidable (a b c d e : Fin 8) :
    Decidable (mongeN8StrongFiveLaws a b c d e) := by
  unfold mongeN8StrongFiveLaws
  infer_instance

/-- Every increasing five-tuple violates at least one of its ten strong-polygon equalities. -/
theorem mongeN8_strongFiveLaws_false :
    ∀ a b c d e : Fin 8, a < b → b < c → c < d → d < e →
      ¬mongeN8StrongFiveLaws a b c d e := by
  intro a b c d e hab hbc hcd hde
  fin_cases a <;> fin_cases b <;> norm_num at hab
  all_goals fin_cases c <;> norm_num at hbc
  all_goals fin_cases d <;> norm_num at hcd
  all_goals fin_cases e <;> norm_num at hde
  all_goals decide

/-- No increasing five-subsequence satisfies the existing strong-polygon law. -/
theorem mongeN8_noStrongFive :
    ∀ f : Fin 5 ↪o Fin 8, ¬IsStrongPolygonOn mongeN8Coloring f := by
  intro f hstrong
  have h01 : f 0 < f 1 := f.strictMono (by decide)
  have h12 : f 1 < f 2 := f.strictMono (by decide)
  have h23 : f 2 < f 3 := f.strictMono (by decide)
  have h34 : f 3 < f 4 := f.strictMono (by decide)
  have h0123 := hstrong (i := (0 : Fin 5)) (j := 1) (k := 2) (l := 3)
    (by decide) (by decide) (by decide)
  have h0124 := hstrong (i := (0 : Fin 5)) (j := 1) (k := 2) (l := 4)
    (by decide) (by decide) (by decide)
  have h0134 := hstrong (i := (0 : Fin 5)) (j := 1) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
  have h0234 := hstrong (i := (0 : Fin 5)) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
  have h1234 := hstrong (i := (1 : Fin 5)) (j := 2) (k := 3) (l := 4)
    (by decide) (by decide) (by decide)
  rw [mongeN8Coloring_eq_table] at h0123 h0124 h0134 h0234 h1234
  apply mongeN8_strongFiveLaws_false (f 0) (f 1) (f 2) (f 3) (f 4)
    h01 h12 h23 h34
  simp only [mongeN8StrongFiveLaws]
  exact ⟨h0123.1, h0123.2, h0124.1, h0124.2, h0134.1,
    h0134.2, h0234.1, h0234.2, h1234.1, h1234.2⟩

/-- Increasing triples have computable equality through their three coordinates. -/
local instance orderedTripleDecidableEq (n : ℕ) : DecidableEq (OrderedTriple n) :=
  fun s t ↦
    if h : s.i = t.i ∧ s.j = t.j ∧ s.k = t.k then
      isTrue (by
        rcases s with ⟨si, sj, sk, hsij, hsjk⟩
        rcases t with ⟨ti, tj, tk, htij, htjk⟩
        simp_all)
    else
      isFalse (by
        intro hst
        apply h
        subst t
        exact ⟨rfl, rfl, rfl⟩)

/-- The 56 increasing triples of `Fin 8`, in lexicographic order. -/
def mongeN8OrderedTriples : List (OrderedTriple 8) := [
  ⟨0, 1, 2, by decide, by decide⟩,
  ⟨0, 1, 3, by decide, by decide⟩,
  ⟨0, 1, 4, by decide, by decide⟩,
  ⟨0, 1, 5, by decide, by decide⟩,
  ⟨0, 1, 6, by decide, by decide⟩,
  ⟨0, 1, 7, by decide, by decide⟩,
  ⟨0, 2, 3, by decide, by decide⟩,
  ⟨0, 2, 4, by decide, by decide⟩,
  ⟨0, 2, 5, by decide, by decide⟩,
  ⟨0, 2, 6, by decide, by decide⟩,
  ⟨0, 2, 7, by decide, by decide⟩,
  ⟨0, 3, 4, by decide, by decide⟩,
  ⟨0, 3, 5, by decide, by decide⟩,
  ⟨0, 3, 6, by decide, by decide⟩,
  ⟨0, 3, 7, by decide, by decide⟩,
  ⟨0, 4, 5, by decide, by decide⟩,
  ⟨0, 4, 6, by decide, by decide⟩,
  ⟨0, 4, 7, by decide, by decide⟩,
  ⟨0, 5, 6, by decide, by decide⟩,
  ⟨0, 5, 7, by decide, by decide⟩,
  ⟨0, 6, 7, by decide, by decide⟩,
  ⟨1, 2, 3, by decide, by decide⟩,
  ⟨1, 2, 4, by decide, by decide⟩,
  ⟨1, 2, 5, by decide, by decide⟩,
  ⟨1, 2, 6, by decide, by decide⟩,
  ⟨1, 2, 7, by decide, by decide⟩,
  ⟨1, 3, 4, by decide, by decide⟩,
  ⟨1, 3, 5, by decide, by decide⟩,
  ⟨1, 3, 6, by decide, by decide⟩,
  ⟨1, 3, 7, by decide, by decide⟩,
  ⟨1, 4, 5, by decide, by decide⟩,
  ⟨1, 4, 6, by decide, by decide⟩,
  ⟨1, 4, 7, by decide, by decide⟩,
  ⟨1, 5, 6, by decide, by decide⟩,
  ⟨1, 5, 7, by decide, by decide⟩,
  ⟨1, 6, 7, by decide, by decide⟩,
  ⟨2, 3, 4, by decide, by decide⟩,
  ⟨2, 3, 5, by decide, by decide⟩,
  ⟨2, 3, 6, by decide, by decide⟩,
  ⟨2, 3, 7, by decide, by decide⟩,
  ⟨2, 4, 5, by decide, by decide⟩,
  ⟨2, 4, 6, by decide, by decide⟩,
  ⟨2, 4, 7, by decide, by decide⟩,
  ⟨2, 5, 6, by decide, by decide⟩,
  ⟨2, 5, 7, by decide, by decide⟩,
  ⟨2, 6, 7, by decide, by decide⟩,
  ⟨3, 4, 5, by decide, by decide⟩,
  ⟨3, 4, 6, by decide, by decide⟩,
  ⟨3, 4, 7, by decide, by decide⟩,
  ⟨3, 5, 6, by decide, by decide⟩,
  ⟨3, 5, 7, by decide, by decide⟩,
  ⟨3, 6, 7, by decide, by decide⟩,
  ⟨4, 5, 6, by decide, by decide⟩,
  ⟨4, 5, 7, by decide, by decide⟩,
  ⟨4, 6, 7, by decide, by decide⟩,
  ⟨5, 6, 7, by decide, by decide⟩]

/-- The explicit lexicographic list as a finset. -/
def mongeN8AllTriples : Finset (OrderedTriple 8) :=
  mongeN8OrderedTriples.toFinset

set_option maxHeartbeats 1000000 in
/-- Every increasing triple of `Fin 8` occurs in the explicit list. -/
theorem mongeN8_mem_allTriples (t : OrderedTriple 8) : t ∈ mongeN8AllTriples := by
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals decide +revert

/-- Any lawful `Fintype` enumeration has the same universal triple finset. -/
theorem mongeN8_univ_eq_allTriples (inst : Fintype (OrderedTriple 8)) :
    @Finset.univ (OrderedTriple 8) inst = mongeN8AllTriples := by
  ext t
  simp only [Finset.mem_univ, mongeN8_mem_allTriples]

/-- Replace the imported noncomputable enumeration by the explicit 56-triple finset. -/
theorem mongeN8_mismatchEnergy_eq_sum (χ : TripleColoring 8) (label : Fin 8 → Bool) :
    mismatchEnergy χ label = ∑ t ∈ mongeN8AllTriples, mismatchAt χ label t := by
  unfold mismatchEnergy
  rw [mongeN8_univ_eq_allTriples]

/-- The frozen base label has crossing-mismatch energy exactly two. -/
theorem mongeN8_baseEnergy : mismatchEnergy mongeN8Coloring mongeN8BaseLabel = 2 := by
  rw [mongeN8_mismatchEnergy_eq_sum, mongeN8Coloring_eq_table]
  decide

/-- Flipping free vertex `1` gives energy exactly 15. -/
theorem mongeN8_flip1Energy : mismatchEnergy mongeN8Coloring mongeN8Flip1 = 15 := by
  rw [mongeN8_mismatchEnergy_eq_sum, mongeN8Coloring_eq_table]
  decide

/-- Flipping free vertex `2` gives energy exactly 12. -/
theorem mongeN8_flip2Energy : mismatchEnergy mongeN8Coloring mongeN8Flip2 = 12 := by
  rw [mongeN8_mismatchEnergy_eq_sum, mongeN8Coloring_eq_table]
  decide

/-- Flipping free vertex `3` gives energy exactly 3. -/
theorem mongeN8_flip3Energy : mismatchEnergy mongeN8Coloring mongeN8Flip3 = 3 := by
  rw [mongeN8_mismatchEnergy_eq_sum, mongeN8Coloring_eq_table]
  decide

/-- Flipping free vertex `4` gives energy exactly 11. -/
theorem mongeN8_flip4Energy : mismatchEnergy mongeN8Coloring mongeN8Flip4 = 11 := by
  rw [mongeN8_mismatchEnergy_eq_sum, mongeN8Coloring_eq_table]
  decide

/-- Flipping free vertex `5` gives energy exactly 19. -/
theorem mongeN8_flip5Energy : mismatchEnergy mongeN8Coloring mongeN8Flip5 = 19 := by
  rw [mongeN8_mismatchEnergy_eq_sum, mongeN8Coloring_eq_table]
  decide

/-- Flipping free vertex `6` gives energy exactly 21. -/
theorem mongeN8_flip6Energy : mismatchEnergy mongeN8Coloring mongeN8Flip6 = 21 := by
  rw [mongeN8_mismatchEnergy_eq_sum, mongeN8Coloring_eq_table]
  decide

/--
The exact realizable eight-point witness is strong-five-free and is a positive strict local
minimum of the crossing-mismatch energy under its six free one-bit flips.
-/
theorem mongeN8_realizable_strictLocalMinimum_counterexample :
    mongeN8Configuration.point = ordinatePoint mongeN8Heights ∧
    mongeN8Configuration.tripleColoring = mongeN8Coloring ∧
    (∀ ⦃i j k : Fin 8⦄, i ≠ j → i ≠ k → j ≠ k →
      orientation (mongeN8Configuration.point i) (mongeN8Configuration.point j)
        (mongeN8Configuration.point k) ≠ 0) ∧
    (∀ f : Fin 5 ↪o Fin 8, ¬IsStrongPolygonOn mongeN8Coloring f) ∧
    mismatchEnergy mongeN8Coloring mongeN8BaseLabel = 2 ∧
    mismatchEnergy mongeN8Coloring mongeN8Flip1 = 15 ∧
    mismatchEnergy mongeN8Coloring mongeN8Flip2 = 12 ∧
    mismatchEnergy mongeN8Coloring mongeN8Flip3 = 3 ∧
    mismatchEnergy mongeN8Coloring mongeN8Flip4 = 11 ∧
    mismatchEnergy mongeN8Coloring mongeN8Flip5 = 19 ∧
    mismatchEnergy mongeN8Coloring mongeN8Flip6 = 21 := by
  exact ⟨rfl, rfl, mongeN8Configuration.generalPosition, mongeN8_noStrongFive,
    mongeN8_baseEnergy, mongeN8_flip1Energy, mongeN8_flip2Energy, mongeN8_flip3Energy,
    mongeN8_flip4Energy, mongeN8_flip5Energy, mongeN8_flip6Energy⟩

end

end CrossingMismatch
end ErdosSzekeres

end
