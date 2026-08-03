module

public import ErdosSzekeres.Decomposable
public import ErdosSzekeres.RankProfile

@[expose] public section

/-!
# A realizable collision for the clipped consecutive pair-rank state

This file kernel-checks the `k = 6`, `n = 9` singleton-root collision found by
the bounded E3 rank/downset gate. Two recursively decomposable colorings have
the same complete left/right pair-rank thresholds through four after removing
vertex `1`, but their full parent states differ. Both colorings are induced by
explicit rational planar configurations, so sweep realizability does not
repair this failed transition.
-/

namespace ErdosSzekeres
namespace RankProfileCollision

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

inductive DecompositionTree (n : ℕ) where
  | leaf : Fin n → DecompositionTree n
  | node : DecompositionTree n → DecompositionTree n → DecompositionTree n

namespace DecompositionTree

def vertices {n : ℕ} : DecompositionTree n → Finset (Fin n)
  | .leaf i => {i}
  | .node lower upper => lower.vertices ∪ upper.vertices

def coloring {n : ℕ} : DecompositionTree n → TripleColoring n
  | .leaf _ => fun _ ↦ Turn.right
  | .node lower upper => fun t ↦
      if t.i ∈ lower.vertices ∧ t.j ∈ lower.vertices ∧ t.k ∈ lower.vertices then
        lower.coloring t
      else if t.i ∈ upper.vertices ∧ t.j ∈ upper.vertices ∧
          t.k ∈ upper.vertices then
        upper.coloring t
      else if t.j ∈ lower.vertices then Turn.left else Turn.right

def WellFormed {n : ℕ} : DecompositionTree n → Prop
  | .leaf _ => True
  | .node lower upper =>
      lower.WellFormed ∧ upper.WellFormed ∧ Disjoint lower.vertices upper.vertices

theorem node_split {n : ℕ} (lower upper : DecompositionTree n)
    (hdisjoint : Disjoint lower.vertices upper.vertices) :
    HasDeepBelowSplit (DecompositionTree.node lower upper).coloring
      lower.vertices upper.vertices := by
  constructor
  · exact hdisjoint
  · intro t _ _ _ hnotLower hnotUpper
    change (if t.i ∈ lower.vertices ∧ t.j ∈ lower.vertices ∧
        t.k ∈ lower.vertices then lower.coloring t
      else if t.i ∈ upper.vertices ∧ t.j ∈ upper.vertices ∧
        t.k ∈ upper.vertices then upper.coloring t
      else if t.j ∈ lower.vertices then Turn.left else Turn.right) = _
    rw [if_neg hnotLower, if_neg hnotUpper]

theorem decomposableOn_congr {n : ℕ} {χ ψ : TripleColoring n}
    {s : Finset (Fin n)} (h : IsDecomposableOn χ s)
    (heq : ∀ t, t.i ∈ s → t.j ∈ s → t.k ∈ s → χ t = ψ t) :
    IsDecomposableOn ψ s := by
  induction h generalizing ψ with
  | singleton i => exact .singleton i
  | @split lower upper hlower hupper hsplit ihlower ihupper =>
      apply IsDecomposableOn.split
      · apply ihlower
        intro t hi hj hk
        exact heq t (Finset.mem_union_left _ hi) (Finset.mem_union_left _ hj)
          (Finset.mem_union_left _ hk)
      · apply ihupper
        intro t hi hj hk
        exact heq t (Finset.mem_union_right _ hi) (Finset.mem_union_right _ hj)
          (Finset.mem_union_right _ hk)
      · constructor
        · exact hsplit.disjoint
        · intro t hi hj hk hnotLower hnotUpper
          rw [← heq t hi hj hk]
          exact hsplit.crossing t hi hj hk hnotLower hnotUpper

theorem decomposableOn {n : ℕ} (tree : DecompositionTree n)
    (h : tree.WellFormed) : IsDecomposableOn tree.coloring tree.vertices := by
  induction tree with
  | leaf i => exact .singleton i
  | node lower upper ihlower ihupper =>
      rcases h with ⟨hlower, hupper, hdisjoint⟩
      apply IsDecomposableOn.split
      · apply decomposableOn_congr (ihlower hlower)
        intro t hi hj hk
        simp [coloring, hi, hj, hk]
      · apply decomposableOn_congr (ihupper hupper)
        intro t hi hj hk
        have hiNot : t.i ∉ lower.vertices := fun hiLower ↦
          Finset.disjoint_left.mp hdisjoint hiLower hi
        simp [coloring, hi, hj, hk, hiNot]
      · exact node_split lower upper hdisjoint

end DecompositionTree

/-- Executable checker for the strong-polygon law on a finite vertex set. -/
def strongPolygonSetBool {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) : Bool :=
  (List.finRange n).all fun i ↦
    (List.finRange n).all fun j ↦
      (List.finRange n).all fun k ↦
        (List.finRange n).all fun l ↦
          if hij : i < j then
            if hjk : j < k then
              if hkl : k < l then
                if i ∈ s ∧ j ∈ s ∧ k ∈ s ∧ l ∈ s then
                  decide (χ ⟨i, j, k, hij, hjk⟩ =
                    χ ⟨i, j, l, hij, hjk.trans hkl⟩) &&
                  decide (χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
                    χ ⟨j, k, l, hjk, hkl⟩)
                else true
              else true
            else true
          else true

theorem strongPolygonSetBool_eq_true_iff {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) :
    strongPolygonSetBool χ s = true ↔ IsStrongPolygonSet χ s := by
  constructor
  · intro h i j k l hij hjk hkl hi hj hk hl
    have hiCheck := (List.all_eq_true.mp h) i (List.mem_finRange i)
    have hjCheck := (List.all_eq_true.mp hiCheck) j (List.mem_finRange j)
    have hkCheck := (List.all_eq_true.mp hjCheck) k (List.mem_finRange k)
    have hlCheck := (List.all_eq_true.mp hkCheck) l (List.mem_finRange l)
    simpa [strongPolygonSetBool, hij, hjk, hkl, hi, hj, hk, hl] using hlCheck
  · intro h
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    apply List.all_eq_true.mpr
    intro k _
    apply List.all_eq_true.mpr
    intro l _
    by_cases hij : i < j
    · by_cases hjk : j < k
      · by_cases hkl : k < l
        · by_cases hi : i ∈ s
          · by_cases hj : j ∈ s
            · by_cases hk : k ∈ s
              · by_cases hl : l ∈ s
                · simp [hij, hjk, hkl, hi, hj, hk, hl,
                    h hij hjk hkl hi hj hk hl]
                · simp [hij, hjk, hkl, hi, hj, hk, hl]
              · simp [hij, hjk, hkl, hi, hj, hk]
            · simp [hij, hjk, hkl, hi, hj]
          · simp [hij, hjk, hkl, hi]
        · simp [hij, hjk, hkl]
      · simp [hij, hjk]
    · simp [hij]

def pairRankLeftUpperTree : DecompositionTree 9 :=
  .node
    (.node (.leaf 8) (.node (.node (.node (.leaf 5) (.leaf 0)) (.leaf 2)) (.leaf 3)))
    (.node (.node (.leaf 7) (.leaf 6)) (.leaf 4))

def pairRankLeftTree : DecompositionTree 9 :=
  .node (.leaf 1) pairRankLeftUpperTree

def pairRankRightUpperTree : DecompositionTree 9 :=
  .node
    (.node (.node (.node (.leaf 8) (.leaf 0)) (.node (.leaf 5) (.leaf 2))) (.leaf 3))
    (.node (.node (.leaf 7) (.leaf 6)) (.leaf 4))

def pairRankRightTree : DecompositionTree 9 :=
  .node (.leaf 1) pairRankRightUpperTree

/-- The first parent coloring in the complete pair-rank collision. -/
def pairRankLeftColor : TripleColoring 9 := pairRankLeftTree.coloring

/-- The second parent coloring in the complete pair-rank collision. -/
def pairRankRightColor : TripleColoring 9 := pairRankRightTree.coloring

/-- The common upper child at the singleton root `{1}`. -/
def pairRankUpper : Finset (Fin 9) := Finset.univ.erase 1

theorem pairRankLeft_noStrongSetBool_six :
    ∀ s : Finset (Fin 9), s.card = 6 →
      strongPolygonSetBool pairRankLeftColor s = false := by
  decide

theorem pairRankRight_noStrongSetBool_six :
    ∀ s : Finset (Fin 9), s.card = 6 →
      strongPolygonSetBool pairRankRightColor s = false := by
  decide

theorem pairRankLeft_open :
    ¬∃ f : Fin 6 ↪o Fin 9, IsStrongPolygonOn pairRankLeftColor f := by
  rintro ⟨f, hstrong⟩
  let s : Finset (Fin 9) := Finset.univ.image f
  have hcard : s.card = 6 := by
    simpa [s] using Finset.card_image_of_injective Finset.univ f.injective
  have hfalse := pairRankLeft_noStrongSetBool_six s hcard
  have htrue := (strongPolygonSetBool_eq_true_iff pairRankLeftColor s).2
    (FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong)
  rw [hfalse] at htrue
  contradiction

theorem pairRankRight_open :
    ¬∃ f : Fin 6 ↪o Fin 9, IsStrongPolygonOn pairRankRightColor f := by
  rintro ⟨f, hstrong⟩
  let s : Finset (Fin 9) := Finset.univ.image f
  have hcard : s.card = 6 := by
    simpa [s] using Finset.card_image_of_injective Finset.univ f.injective
  have hfalse := pairRankRight_noStrongSetBool_six s hcard
  have htrue := (strongPolygonSetBool_eq_true_iff pairRankRightColor s).2
    (FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong)
  rw [hfalse] at htrue
  contradiction

theorem pairRankLeft_root :
    HasDeepBelowSplit pairRankLeftColor {1} pairRankUpper := by
  have h := DecompositionTree.node_split
    (DecompositionTree.leaf 1) pairRankLeftUpperTree (by decide)
  have hupper : pairRankLeftUpperTree.vertices = pairRankUpper := by decide
  rw [hupper] at h
  exact h

theorem pairRankRight_root :
    HasDeepBelowSplit pairRankRightColor {1} pairRankUpper := by
  have h := DecompositionTree.node_split
    (DecompositionTree.leaf 1) pairRankRightUpperTree (by decide)
  have hupper : pairRankRightUpperTree.vertices = pairRankUpper := by decide
  rw [hupper] at h
  exact h

theorem pairRankLeft_decomposable : IsDecomposable pairRankLeftColor := by
  have hwell : pairRankLeftTree.WellFormed := by
    simp [pairRankLeftTree, pairRankLeftUpperTree, DecompositionTree.WellFormed,
      DecompositionTree.vertices]
  have h := DecompositionTree.decomposableOn pairRankLeftTree hwell
  have hvertices : pairRankLeftTree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h

theorem pairRankRight_decomposable : IsDecomposable pairRankRightColor := by
  have hwell : pairRankRightTree.WellFormed := by
    simp [pairRankRightTree, pairRankRightUpperTree, DecompositionTree.WellFormed,
      DecompositionTree.vertices]
  have h := DecompositionTree.decomposableOn pairRankRightTree hwell
  have hvertices : pairRankRightTree.vertices = Finset.univ := by decide
  rw [hvertices] at h
  exact h

theorem pairRank_child_state_equal :
    RankProfile.FinitePairRankStateEq
      pairRankLeftColor pairRankRightColor pairRankUpper 4 := by
  intro u v q
  fin_cases u <;> fin_cases v <;> fin_cases q <;> decide

theorem pairRank_parent_cap_difference :
    RankProfile.HasFinitePairRankAbove
        pairRankLeftColor Turn.right Finset.univ 5 8 3 ∧
      ¬RankProfile.HasFinitePairRankAbove
        pairRankRightColor Turn.right Finset.univ 5 8 3 := by
  constructor <;> decide

theorem pairRank_parent_state_ne :
    ¬RankProfile.FinitePairRankStateEq
      pairRankLeftColor pairRankRightColor Finset.univ 4 := by
  intro h
  exact pairRank_parent_cap_difference.2
    ((h 5 8 ⟨3, by decide⟩).2.mp pairRank_parent_cap_difference.1)

/-- Rational coordinates realizing the first collision coloring with `x_i=i`. -/
noncomputable def pairRankLeftPoints : Fin 9 → Point 2 := ![
  ![0, 0], ![1, -(1765 : ℝ) / 112], ![2, (5 : ℝ) / 8],
  ![3, (23 : ℝ) / 16], ![4, (131 : ℝ) / 28], ![5, (17 : ℝ) / 16],
  ![6, (281 : ℝ) / 56], ![7, (91 : ℝ) / 16], ![8, 0]]

/-- Rational coordinates realizing the second collision coloring with `x_i=i`. -/
noncomputable def pairRankRightPoints : Fin 9 → Point 2 := ![
  ![0, 0], ![1, -(334 : ℝ) / 21], ![2, (1 : ℝ) / 3],
  ![3, 1], ![4, (86 : ℝ) / 21], ![5, (1 : ℝ) / 3],
  ![6, (29 : ℝ) / 7], ![7, (14 : ℝ) / 3], ![8, 0]]

noncomputable def pairRankLeftConfiguration : SweptConfiguration 9 where
  point := pairRankLeftPoints
  sweep_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num [pairRankLeftPoints]
  generalPosition := generalPosition_of_ordered pairRankLeftPoints (by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals norm_num at hij
    all_goals norm_num at hjk
    all_goals norm_num [pairRankLeftPoints, orientation])

noncomputable def pairRankRightConfiguration : SweptConfiguration 9 where
  point := pairRankRightPoints
  sweep_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    all_goals norm_num [pairRankRightPoints]
  generalPosition := generalPosition_of_ordered pairRankRightPoints (by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals norm_num at hij
    all_goals norm_num at hjk
    all_goals norm_num [pairRankRightPoints, orientation])

theorem pairRankLeftConfiguration_coloring :
    pairRankLeftConfiguration.tripleColoring = pairRankLeftColor := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [pairRankLeftConfiguration, pairRankLeftPoints,
      SweptConfiguration.tripleColoring, SweptConfiguration.turn,
      pairRankLeftColor, pairRankLeftTree, pairRankLeftUpperTree,
      DecompositionTree.coloring, DecompositionTree.vertices, orientation]
  all_goals simp_all

theorem pairRankRightConfiguration_coloring :
    pairRankRightConfiguration.tripleColoring = pairRankRightColor := by
  funext t
  rcases t with ⟨i, j, k, hij, hjk⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [pairRankRightConfiguration, pairRankRightPoints,
      SweptConfiguration.tripleColoring, SweptConfiguration.turn,
      pairRankRightColor, pairRankRightTree, pairRankRightUpperTree,
      DecompositionTree.coloring, DecompositionTree.vertices, orientation]
  all_goals simp_all

theorem pairRankLeft_realizable : IsSweepRealizable pairRankLeftColor :=
  ⟨pairRankLeftConfiguration, pairRankLeftConfiguration_coloring⟩

theorem pairRankRight_realizable : IsSweepRealizable pairRankRightColor :=
  ⟨pairRankRightConfiguration, pairRankRightConfiguration_coloring⟩

/-- The complete child pair-rank matrix is not a congruence for the fixed
singleton-root transition, even for sweep-realizable decomposable colorings. -/
theorem exists_realizable_pairRankState_collision :
    ∃ χ ψ : TripleColoring 9,
      IsSweepRealizable χ ∧ IsSweepRealizable ψ ∧
      IsDecomposable χ ∧ IsDecomposable ψ ∧
      HasDeepBelowSplit χ {1} pairRankUpper ∧
      HasDeepBelowSplit ψ {1} pairRankUpper ∧
      (¬∃ f : Fin 6 ↪o Fin 9, IsStrongPolygonOn χ f) ∧
      (¬∃ f : Fin 6 ↪o Fin 9, IsStrongPolygonOn ψ f) ∧
      RankProfile.FinitePairRankStateEq χ ψ pairRankUpper 4 ∧
      ¬RankProfile.FinitePairRankStateEq χ ψ Finset.univ 4 := by
  exact ⟨pairRankLeftColor, pairRankRightColor,
    pairRankLeft_realizable, pairRankRight_realizable,
    pairRankLeft_decomposable, pairRankRight_decomposable,
    pairRankLeft_root, pairRankRight_root,
    pairRankLeft_open, pairRankRight_open,
    pairRank_child_state_equal, pairRank_parent_state_ne⟩

end RankProfileCollision
end ErdosSzekeres
