module

public import ErdosSzekeres.StructuralChargingNextState578Regeneration
public import ErdosSzekeres.RankProfileCollision
public import ErdosSzekeres.DecomposableRealization

@[expose] public section

/-!
# A target-free three-cup regeneration configuration

The three disjoint four-cups and a covering four-cap obtained from the
color-dual packing do not by themselves force a five-cup, seven-cap, or strong
eight-set.  This file kernel-checks a minimal twelve-vertex recursively
decomposable counterexample.  The same coloring realizes both possible cap
incidence profiles, `2+2+0` and `2+1+1`.

The example does not carry the additional twenty vertices, the three disjoint
external caps, or the singleton-root data of the live 32-vertex gate.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578RegenerationCounterexample

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

def cupOneTree : RankProfileCollision.DecompositionTree 12 :=
  .node (.node (.leaf 1) (.leaf 3)) (.node (.leaf 0) (.leaf 11))

def cupTwoTree : RankProfileCollision.DecompositionTree 12 :=
  .node (.node (.leaf 8) (.leaf 9)) (.node (.leaf 2) (.leaf 10))

def lowerTree : RankProfileCollision.DecompositionTree 12 :=
  .node cupOneTree cupTwoTree

def cupThreeTree : RankProfileCollision.DecompositionTree 12 :=
  .node (.node (.leaf 5) (.leaf 6)) (.node (.leaf 4) (.leaf 7))

def tree : RankProfileCollision.DecompositionTree 12 :=
  .node lowerTree cupThreeTree

/-- Local executable copy of the tree-support recursion. -/
def treeVertices {n : ℕ} : RankProfileCollision.DecompositionTree n →
    Finset (Fin n)
  | .leaf i => {i}
  | .node lower upper => treeVertices lower ∪ treeVertices upper

/-- Local executable copy of the recursive deep-below coloring. -/
def treeColoring {n : ℕ} : RankProfileCollision.DecompositionTree n →
    TripleColoring n
  | .leaf _ => fun _ ↦ .right
  | .node lower upper => fun t ↦
      if t.i ∈ treeVertices lower ∧ t.j ∈ treeVertices lower ∧
          t.k ∈ treeVertices lower then
        treeColoring lower t
      else if t.i ∈ treeVertices upper ∧ t.j ∈ treeVertices upper ∧
          t.k ∈ treeVertices upper then
        treeColoring upper t
      else if t.j ∈ treeVertices lower then .left else .right

theorem treeVertices_eq_vertices {n : ℕ}
    (candidate : RankProfileCollision.DecompositionTree n) :
    treeVertices candidate = candidate.vertices := by
  induction candidate with
  | leaf i => rfl
  | node lower upper ihLower ihUpper =>
      simp only [treeVertices,
        RankProfileCollision.DecompositionTree.vertices, ihLower, ihUpper]

theorem treeColoring_eq_coloring {n : ℕ}
    (candidate : RankProfileCollision.DecompositionTree n) :
    treeColoring candidate = candidate.coloring := by
  induction candidate with
  | leaf i => rfl
  | node lower upper ihLower ihUpper =>
      funext t
      simp only [treeColoring,
        RankProfileCollision.DecompositionTree.coloring,
        treeVertices_eq_vertices, ihLower, ihUpper]

def color : TripleColoring 12 := treeColoring tree

def support : Finset (Fin 12) := treeVertices tree

def cup₁ : Finset (Fin 12) := {0, 1, 3, 11}

def cup₂ : Finset (Fin 12) := {2, 8, 9, 10}

def cup₃ : Finset (Fin 12) := {4, 5, 6, 7}

def cap₂₂₀ : Finset (Fin 12) := {0, 2, 8, 11}

def cap₂₁₁ : Finset (Fin 12) := {0, 4, 5, 8}

/-- Executable equality on turns for native certificate evaluation. -/
def turnEq : Turn → Turn → Bool
  | .left, .left => true
  | .right, .right => true
  | _, _ => false

theorem turnEq_eq_true_iff (first second : Turn) :
    turnEq first second = true ↔ first = second := by
  cases first <;> cases second <;> decide

theorem turnEq_self (turn : Turn) : turnEq turn turn = true := by
  cases turn <;> rfl

/-- Executable monochromaticity check for the concrete coloring. -/
def turnSetBool (s : Finset (Fin 12)) (turn : Turn) : Bool :=
  (List.finRange 12).all fun i ↦
    (List.finRange 12).all fun j ↦
      (List.finRange 12).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              turnEq (color ⟨i, j, k, hij, hjk⟩) turn
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 12)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 12, t.i ∈ s → t.j ∈ s → t.k ∈ s →
        color t = turn := by
  constructor
  · intro h t hi hj hk
    have hiCheck := (List.all_eq_true.mp h) t.i (List.mem_finRange t.i)
    have hjCheck := (List.all_eq_true.mp hiCheck) t.j (List.mem_finRange t.j)
    have hkCheck := (List.all_eq_true.mp hjCheck) t.k (List.mem_finRange t.k)
    apply (turnEq_eq_true_iff _ _).mp
    simpa [turnSetBool, t.hij, t.hjk, hi, hj, hk] using hkCheck
  · intro h
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    apply List.all_eq_true.mpr
    intro k _
    by_cases hij : i < j
    · by_cases hjk : j < k
      · by_cases hi : i ∈ s
        · by_cases hj : j ∈ s
          · by_cases hk : k ∈ s
            · simp [hij, hjk, hi, hj, hk,
                h ⟨i, j, k, hij, hjk⟩ hi hj hk, turnEq_self]
            · simp [hij, hjk, hi, hj, hk]
          · simp [hij, hjk, hi, hj]
        · simp [hij, hjk, hi]
      · simp [hij, hjk]
    · simp [hij]

/-- Executable checker for the strong-polygon equations. -/
def strongPolygonSetBool (s : Finset (Fin 12)) : Bool :=
  (List.finRange 12).all fun i ↦
    (List.finRange 12).all fun j ↦
      (List.finRange 12).all fun k ↦
        (List.finRange 12).all fun l ↦
          if hij : i < j then
            if hjk : j < k then
              if hkl : k < l then
                if i ∈ s ∧ j ∈ s ∧ k ∈ s ∧ l ∈ s then
                  turnEq
                    (color ⟨i, j, k, hij, hjk⟩)
                    (color ⟨i, j, l, hij, hjk.trans hkl⟩) &&
                  turnEq
                    (color ⟨i, k, l, hij.trans hjk, hkl⟩)
                    (color ⟨j, k, l, hjk, hkl⟩)
                else true
              else true
            else true
          else true

theorem strongPolygonSetBool_eq_true_iff (s : Finset (Fin 12)) :
    strongPolygonSetBool s = true ↔ IsStrongPolygonSet color s := by
  constructor
  · intro h i j k l hij hjk hkl hi hj hk hl
    have hiCheck := (List.all_eq_true.mp h) i (List.mem_finRange i)
    have hjCheck := (List.all_eq_true.mp hiCheck) j (List.mem_finRange j)
    have hkCheck := (List.all_eq_true.mp hjCheck) k (List.mem_finRange k)
    have hlCheck := (List.all_eq_true.mp hkCheck) l (List.mem_finRange l)
    have hcheck :
        (turnEq
            (color ⟨i, j, k, hij, hjk⟩)
            (color ⟨i, j, l, hij, hjk.trans hkl⟩) &&
          turnEq
            (color ⟨i, k, l, hij.trans hjk, hkl⟩)
            (color ⟨j, k, l, hjk, hkl⟩)) = true := by
      simpa [strongPolygonSetBool, hij, hjk, hkl, hi, hj, hk, hl]
        using hlCheck
    have hpairs := Bool.and_eq_true_iff.mp hcheck
    exact ⟨(turnEq_eq_true_iff _ _).mp hpairs.1,
      (turnEq_eq_true_iff _ _).mp hpairs.2⟩
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
                · have heq := h hij hjk hkl hi hj hk hl
                  simp [hij, hjk, hkl, hi, hj, hk, hl,
                    heq.1, heq.2, turnEq_self]
                · simp [hij, hjk, hkl, hi, hj, hk, hl]
              · simp [hij, hjk, hkl, hi, hj, hk]
            · simp [hij, hjk, hkl, hi, hj]
          · simp [hij, hjk, hkl, hi]
        · simp [hij, hjk, hkl]
      · simp [hij, hjk]
    · simp [hij]

theorem tree_wellFormed : tree.WellFormed := by
  simp [tree, lowerTree, cupOneTree, cupTwoTree, cupThreeTree,
    RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem support_eq_univ : support = Finset.univ := by decide

theorem support_decomposable : IsDecomposableOn color support :=
  by
    simpa [color, support, treeVertices_eq_vertices,
      treeColoring_eq_coloring] using tree.decomposableOn tree_wellFormed

theorem color_decomposable : IsDecomposable color := by
  simpa [IsDecomposable, support_eq_univ] using support_decomposable

theorem color_sweepRealizable : IsSweepRealizable color :=
  color_decomposable.isSweepRealizable

theorem cup₁_mem : cup₁ ∈ capWitnesses color.dual support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  apply isCapSet_dual_iff.mpr
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff cup₁ .left).mp (by decide)

theorem cup₂_mem : cup₂ ∈ capWitnesses color.dual support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  apply isCapSet_dual_iff.mpr
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff cup₂ .left).mp (by decide)

theorem cup₃_mem : cup₃ ∈ capWitnesses color.dual support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  apply isCapSet_dual_iff.mpr
  simpa [IsCupSet] using
    (turnSetBool_eq_true_iff cup₃ .left).mp (by decide)

theorem cap₂₂₀_mem : cap₂₂₀ ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff cap₂₂₀ .right).mp (by decide)

theorem cap₂₁₁_mem : cap₂₁₁ ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff cap₂₁₁ .right).mp (by decide)

theorem cups_partition_support : support = cup₁ ∪ cup₂ ∪ cup₃ := by decide

theorem cup₁_cup₂ : Disjoint cup₁ cup₂ := by decide

theorem cup₁_cup₃ : Disjoint cup₁ cup₃ := by decide

theorem cup₂_cup₃ : Disjoint cup₂ cup₃ := by decide

def configuration₂₂₀ :
    ThreeCupRegenerationConfiguration578 color support where
  cup₁ := cup₁
  cup₂ := cup₂
  cup₃ := cup₃
  cap := cap₂₂₀
  cup₁_mem := cup₁_mem
  cup₂_mem := cup₂_mem
  cup₃_mem := cup₃_mem
  cap_mem := cap₂₂₀_mem
  cup₁_cup₂ := cup₁_cup₂
  cup₁_cup₃ := cup₁_cup₃
  cup₂_cup₃ := cup₂_cup₃
  support_eq := cups_partition_support

def configuration₂₁₁ :
    ThreeCupRegenerationConfiguration578 color support where
  cup₁ := cup₁
  cup₂ := cup₂
  cup₃ := cup₃
  cap := cap₂₁₁
  cup₁_mem := cup₁_mem
  cup₂_mem := cup₂_mem
  cup₃_mem := cup₃_mem
  cap_mem := cap₂₁₁_mem
  cup₁_cup₂ := cup₁_cup₂
  cup₁_cup₃ := cup₁_cup₃
  cup₂_cup₃ := cup₂_cup₃
  support_eq := cups_partition_support

theorem cap₂₂₀_incidence :
    TwoTwoZeroCupIncidence578 cap₂₂₀ cup₁ cup₂ cup₃ := by
  simp [TwoTwoZeroCupIncidence578, cap₂₂₀, cup₁, cup₂, cup₃]

theorem cap₂₁₁_incidence :
    TwoOneOneCupIncidence578 cap₂₁₁ cup₁ cup₂ cup₃ := by
  simp [TwoOneOneCupIncidence578, cap₂₁₁, cup₁, cup₂, cup₃]

/-- The exact target-free `2+1+1` model even contains a vertex which is a
sweep-middle vertex of both the third cup and the regenerated cap.  The local
shared-middle theorem is nevertheless satisfied because that cup is wholly
in the root's upper child. -/
theorem cap₂₁₁_shared_middle_has_safe_whole_upper :
    let q : Fin 12 := 5
    q ∈ cup₃ ∩ cap₂₁₁ ∧
      ¬HasDeepBelowSplit.IsSweepEndpoint cup₃ q ∧
      ¬HasDeepBelowSplit.IsSweepEndpoint cap₂₁₁ q ∧
      cup₃ ⊆ treeVertices cupThreeTree := by
  norm_num [cup₃, cap₂₁₁, cupThreeTree, treeVertices,
    HasDeepBelowSplit.IsSweepEndpoint,
    HasDeepBelowSplit.IsLeftSweepEndpoint,
    HasDeepBelowSplit.IsRightSweepEndpoint]
  all_goals omega

theorem no_cup_five_bool :
    ∀ s : Finset (Fin 12), s.card = 5 → turnSetBool s .left = false := by
  native_decide

/-- The example is stronger than required: it has no five-cap either. -/
theorem no_cap_five_bool :
    ∀ s : Finset (Fin 12), s.card = 5 → turnSetBool s .right = false := by
  native_decide

theorem no_cap_seven_bool :
    ∀ s : Finset (Fin 12), s.card = 7 → turnSetBool s .right = false := by
  native_decide

theorem no_strong_eight_bool :
    ∀ s : Finset (Fin 12), s.card = 8 →
      strongPolygonSetBool s = false := by
  native_decide

theorem no_cup_five : ¬ContainsCupSet color support 5 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cup_five_bool witness hcard
  have htrue : turnSetBool witness .left = true :=
    (turnSetBool_eq_true_iff witness .left).mpr (by
      simpa [IsCupSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_cap_five : ¬ContainsCapSet color support 5 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cap_five_bool witness hcard
  have htrue : turnSetBool witness .right = true :=
    (turnSetBool_eq_true_iff witness .right).mpr (by
      simpa [IsCapSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_cap_seven : ¬ContainsCapSet color support 7 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cap_seven_bool witness hcard
  have htrue : turnSetBool witness .right = true :=
    (turnSetBool_eq_true_iff witness .right).mpr (by
      simpa [IsCapSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_strong_eight : ¬ContainsStrongPolygonSet color support 8 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_strong_eight_bool witness hcard
  have htrue :=
    (strongPolygonSetBool_eq_true_iff witness).2 hwitness
  rw [hfalse] at htrue
  contradiction

/-- A minimal decomposable coloring realizes both covering-cap incidence
profiles while avoiding every local `(7,5,8)` target. -/
theorem both_regeneration_profiles_are_target_free :
    IsDecomposable color ∧
    IsSweepRealizable color ∧
    Nonempty (ThreeCupRegenerationConfiguration578 color support) ∧
    TwoTwoZeroCupIncidence578 cap₂₂₀ cup₁ cup₂ cup₃ ∧
    Nonempty (ThreeCupRegenerationConfiguration578 color support) ∧
    TwoOneOneCupIncidence578 cap₂₁₁ cup₁ cup₂ cup₃ ∧
    ¬ContainsCapSet color support 5 ∧
    ¬ContainsCupSet color support 5 ∧
    ¬ContainsCapSet color support 7 ∧
    ¬ContainsStrongPolygonSet color support 8 := by
  exact ⟨color_decomposable, color_sweepRealizable,
    ⟨configuration₂₂₀⟩, cap₂₂₀_incidence,
    ⟨configuration₂₁₁⟩, cap₂₁₁_incidence, no_cap_five, no_cup_five,
    no_cap_seven, no_strong_eight⟩

/-- Fully explicit existential form of the obstruction. -/
theorem exists_threeCup_coveringCaps_avoidingTarget578 :
    ∃ (χ : TripleColoring 12)
      (firstCup secondCup thirdCup firstCap secondCap : Finset (Fin 12)),
      IsDecomposable χ ∧
      IsSweepRealizable χ ∧
      Finset.univ = firstCup ∪ secondCup ∪ thirdCup ∧
      firstCup ∈ capWitnesses χ.dual Finset.univ 4 ∧
      secondCup ∈ capWitnesses χ.dual Finset.univ 4 ∧
      thirdCup ∈ capWitnesses χ.dual Finset.univ 4 ∧
      Disjoint firstCup secondCup ∧ Disjoint firstCup thirdCup ∧
      Disjoint secondCup thirdCup ∧
      firstCap ∈ capWitnesses χ Finset.univ 4 ∧
      TwoTwoZeroCupIncidence578 firstCap firstCup secondCup thirdCup ∧
      secondCap ∈ capWitnesses χ Finset.univ 4 ∧
      TwoOneOneCupIncidence578 secondCap firstCup secondCup thirdCup ∧
      ¬ContainsCapSet χ Finset.univ 5 ∧
      ¬ContainsCupSet χ Finset.univ 5 ∧
      ¬ContainsCapSet χ Finset.univ 7 ∧
      ¬ContainsStrongPolygonSet χ Finset.univ 8 := by
  refine ⟨color, cup₁, cup₂, cup₃, cap₂₂₀, cap₂₁₁,
    color_decomposable, color_sweepRealizable, ?_, ?_, ?_, ?_,
    cup₁_cup₂, cup₁_cup₃,
    cup₂_cup₃, ?_, cap₂₂₀_incidence, ?_, cap₂₁₁_incidence,
    ?_, ?_, ?_, ?_⟩
  · simpa [support_eq_univ] using cups_partition_support
  · simpa [support_eq_univ] using cup₁_mem
  · simpa [support_eq_univ] using cup₂_mem
  · simpa [support_eq_univ] using cup₃_mem
  · simpa [support_eq_univ] using cap₂₂₀_mem
  · simpa [support_eq_univ] using cap₂₁₁_mem
  · simpa [support_eq_univ] using no_cap_five
  · simpa [support_eq_univ] using no_cup_five
  · simpa [support_eq_univ] using no_cap_seven
  · simpa [support_eq_univ] using no_strong_eight

end StructuralChargingNextState578RegenerationCounterexample
end ErdosSzekeres

end
