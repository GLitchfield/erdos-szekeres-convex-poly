module

public import ErdosSzekeres.PredecessorHalfFin15CrossExterior

@[expose] public section

/-!
# Triple-owner cross-exterior falsification at fifteen points

This module tests the exact triple-owner/residue-two contract.  The concrete
coloring below is induced by integer ordinates over the fixed sweep order; all
of the finite claims are checked by transparent kernel reduction.
-/

namespace ErdosSzekeres
namespace Fin15TripleCrossCounterexample

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Integer ordinates for the exact fifteen-vertex coloring. -/
def height : Fin 15 → ℤ :=
  ![787561, 250011, 397116, -31310, -189870,
    -513758, 569602, 471981, 496506, 822178,
    -663215, 90488, -573297, 405623, 735430]

/-- Twice the signed area, with the common horizontal spacing cleared. -/
def orientationTwice (i j k : Fin 15) : ℤ :=
  ((j.val : ℤ) - (i.val : ℤ)) * (height k - height i) -
    (height j - height i) * ((k.val : ℤ) - (i.val : ℤ))

/-- The executable orientation coloring of the integer configuration. -/
def color : TripleColoring 15 := fun t ↦
  if 0 < orientationTwice t.i t.j t.k then Turn.left else Turn.right

/-- The seven support vertices in the counterexample. -/
def support : Finset (Fin 15) := {1, 3, 4, 5, 7, 8, 9}

def block0 : Finset (Fin 15) := {5, 7, 8, 9}
def block1 : Finset (Fin 15) := {3, 4, 8, 9}
def block2 : Finset (Fin 15) := {3, 4, 5, 7}
def block3 : Finset (Fin 15) := {1, 4, 7, 8}
def block4 : Finset (Fin 15) := {1, 4, 5, 9}
def block5 : Finset (Fin 15) := {1, 3, 7, 9}
def block6 : Finset (Fin 15) := {1, 3, 5, 8}

/-- The seven Fano-complement blocks, with one duplicate in the eighth slot. -/
def indexedBlock : Fin 8 → Finset (Fin 15) :=
  ![block0, block1, block2, block3, block4, block5, block6, block5]

def blocks : Finset (Finset (Fin 15)) := Finset.univ.image indexedBlock

def q : Fin 15 := 0
def r : Fin 15 := 2
def s : Fin 15 := 6
def x : Fin 15 := 1
def y : Fin 15 := 9
def residue : Finset (Fin 15) := {7, 8}
def ambient : Finset (Fin 15) := insert q (insert r (insert s support))

/-- Executable checker for the strong-polygon law on one finite set. -/
def strongPolygonSetBool (chi : TripleColoring 15)
    (polygon : Finset (Fin 15)) : Bool :=
  (List.finRange 15).all fun i ↦
    (List.finRange 15).all fun j ↦
      (List.finRange 15).all fun k ↦
        (List.finRange 15).all fun l ↦
          if hij : i < j then
            if hjk : j < k then
              if hkl : k < l then
                if i ∈ polygon ∧ j ∈ polygon ∧ k ∈ polygon ∧ l ∈ polygon then
                  decide (chi ⟨i, j, k, hij, hjk⟩ =
                    chi ⟨i, j, l, hij, hjk.trans hkl⟩) &&
                  decide (chi ⟨i, k, l, hij.trans hjk, hkl⟩ =
                    chi ⟨j, k, l, hjk, hkl⟩)
                else true
              else true
            else true
          else true

/-- The executable checker is equivalent to the logical strong-set law. -/
theorem strongPolygonSetBool_eq_true_iff (chi : TripleColoring 15)
    (polygon : Finset (Fin 15)) :
    strongPolygonSetBool chi polygon = true ↔
      IsStrongPolygonSet chi polygon := by
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
        · by_cases hi : i ∈ polygon
          · by_cases hj : j ∈ polygon
            · by_cases hk : k ∈ polygon
              · by_cases hl : l ∈ polygon
                · simp [hij, hjk, hkl, hi, hj, hk, hl,
                    h hij hjk hkl hi hj hk hl]
                · simp [hij, hjk, hkl, hi, hj, hk, hl]
              · simp [hij, hjk, hkl, hi, hj, hk]
            · simp [hij, hjk, hkl, hi, hj]
          · simp [hij, hjk, hkl, hi]
        · simp [hij, hjk, hkl]
      · simp [hij, hjk]
    · simp [hij]

local instance decidableIsStrongPolygonSet (chi : TripleColoring 15)
    (polygon : Finset (Fin 15)) : Decidable (IsStrongPolygonSet chi polygon) :=
  decidable_of_iff (strongPolygonSetBool chi polygon = true)
    (strongPolygonSetBool_eq_true_iff chi polygon)

local instance decidableContainsStrongPolygonSet :
    Decidable (ContainsStrongPolygonSet color ambient 6) := by
  unfold ContainsStrongPolygonSet
  infer_instance

/-- The ten active vertices contain no strong six-set. -/
theorem color_noStrongSix : ¬ContainsStrongPolygonSet color ambient 6 := by
  decide

/-- Executable form of the eight allowed four-turn sequences. -/
def turnSequenceAllowedBool : Turn → Turn → Turn → Turn → Bool
  | .left, .left, .left, .left => true
  | .left, .left, .left, .right => true
  | .left, .left, .right, .right => true
  | .left, .right, .right, .right => true
  | .right, .right, .right, .right => true
  | .right, .right, .right, .left => true
  | .right, .right, .left, .left => true
  | .right, .left, .left, .left => true
  | _, _, _, _ => false

theorem turnSequenceAllowedBool_eq_true_iff (a b c d : Turn) :
    turnSequenceAllowedBool a b c d = true ↔ TurnSequenceAllowed a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [turnSequenceAllowedBool, TurnSequenceAllowed]

/-- Executable checker for the one-change law on the full fifteen vertices. -/
def oneChangeOnUnivBool (chi : TripleColoring 15) : Bool :=
  (List.finRange 15).all fun i ↦
    (List.finRange 15).all fun j ↦
      (List.finRange 15).all fun k ↦
        (List.finRange 15).all fun l ↦
          if hij : i < j then
            if hjk : j < k then
              if hkl : k < l then
                turnSequenceAllowedBool
                  (chi ⟨i, j, k, hij, hjk⟩)
                  (chi ⟨i, j, l, hij, hjk.trans hkl⟩)
                  (chi ⟨i, k, l, hij.trans hjk, hkl⟩)
                  (chi ⟨j, k, l, hjk, hkl⟩)
              else true
            else true
          else true

/-- The executable full-universe checker is equivalent to `OneChangeOn`. -/
theorem oneChangeOnUnivBool_eq_true_iff (chi : TripleColoring 15) :
    oneChangeOnUnivBool chi = true ↔ OneChangeOn chi Finset.univ := by
  constructor
  · intro h i j k l hij hjk hkl _ _ _ _
    have hiCheck := (List.all_eq_true.mp h) i (List.mem_finRange i)
    have hjCheck := (List.all_eq_true.mp hiCheck) j (List.mem_finRange j)
    have hkCheck := (List.all_eq_true.mp hjCheck) k (List.mem_finRange k)
    have hlCheck := (List.all_eq_true.mp hkCheck) l (List.mem_finRange l)
    apply (turnSequenceAllowedBool_eq_true_iff _ _ _ _).mp
    simpa [oneChangeOnUnivBool, hij, hjk, hkl] using hlCheck
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
        · have ht := (turnSequenceAllowedBool_eq_true_iff _ _ _ _).mpr
              (h hij hjk hkl (by simp) (by simp) (by simp) (by simp))
          simpa [oneChangeOnUnivBool, hij, hjk, hkl] using ht
        · simp [oneChangeOnUnivBool, hij, hjk, hkl]
      · simp [oneChangeOnUnivBool, hij, hjk]
    · simp [oneChangeOnUnivBool, hij]

/-- The determinant coloring satisfies the complete one-change law. -/
theorem color_oneChange : OneChangeOn color Finset.univ := by
  apply (oneChangeOnUnivBool_eq_true_iff color).mp
  decide

theorem support_card : support.card = 7 := by
  decide

theorem indexedBlock_sub (i : Fin 8) : indexedBlock i ⊆ support := by
  fin_cases i <;> decide

theorem indexedBlock_card (i : Fin 8) : (indexedBlock i).card = 4 := by
  fin_cases i <;> decide

theorem indexedBlock_small_inter (i j : Fin 8)
    (hne : indexedBlock i ≠ indexedBlock j) :
    (indexedBlock i ∩ indexedBlock j).card ≤ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [indexedBlock, block0, block1, block2, block3, block4, block5,
      block6]

theorem blocks_card : blocks.card = 7 := by
  decide

theorem block_sub (block : Finset (Fin 15)) (hblock : block ∈ blocks) :
    block ⊆ support := by
  rw [blocks] at hblock
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hblock
  exact indexedBlock_sub i

theorem block_card (block : Finset (Fin 15)) (hblock : block ∈ blocks) :
    block.card = 4 := by
  rw [blocks] at hblock
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hblock
  exact indexedBlock_card i

/-- The concrete seven blocks satisfy the exact Fano complement-pair law. -/
theorem fano_pair_complement :
    ∀ pair : Finset (Fin 15), pair ⊆ support → pair.card = 2 →
      ∃! block : Finset (Fin 15), block ∈ blocks ∧ pair ⊆ support \ block := by
  have hclassification := eight_fourBlock_family_fano_classification
    support indexedBlock support_card indexedBlock_sub indexedBlock_card
      indexedBlock_small_inter
  exact hclassification.2.1 blocks_card

theorem block1_mem : block1 ∈ blocks := by
  decide

theorem block5_mem : block5 ∈ blocks := by
  decide

theorem q_outside : q ∈ Finset.univ \ support := by
  decide

theorem r_outside : r ∈ Finset.univ \ support := by
  decide

theorem s_outside : s ∈ Finset.univ \ support := by
  decide

theorem q_ne_r : q ≠ r := by decide
theorem q_ne_s : q ≠ s := by decide
theorem r_ne_s : r ≠ s := by decide

theorem q_owner_strong : IsStrongPolygonSet color (insert q block5) := by
  apply (strongPolygonSetBool_eq_true_iff color _).mp
  decide

theorem r_owner_strong : IsStrongPolygonSet color (insert r block5) := by
  apply (strongPolygonSetBool_eq_true_iff color _).mp
  decide

theorem s_owner_strong : IsStrongPolygonSet color (insert s block1) := by
  apply (strongPolygonSetBool_eq_true_iff color _).mp
  decide

theorem first_killed : ¬block5 ⊆ (support.erase x).erase y := by
  decide

theorem second_killed : ¬block5 ⊆ (support.erase x).erase y := by
  decide

theorem third_killed : ¬block1 ⊆ (support.erase x).erase y := by
  decide

theorem residue_sub : residue ⊆ (support.erase x).erase y := by
  decide

theorem residue_card : residue.card = 2 := by
  decide

theorem triple_residue_strong :
    IsStrongPolygonSet color (insert q (insert r (insert s residue))) := by
  apply (strongPolygonSetBool_eq_true_iff color _).mp
  decide

/-- No conclusion of the frozen helper exists for the concrete premises. -/
theorem no_crossExterior_extension :
    ¬∃ polygon : Finset (Fin 15), ∃ z : Fin 15,
      polygon ⊆ insert q (insert r (insert s support)) ∧
      polygon.card = 5 ∧
      IsStrongPolygonSet color polygon ∧
      z ∈ (block5 ∪ block5 ∪ block1) \ polygon ∧
      IsStrongPolygonSet color (insert z polygon) := by
  rintro ⟨polygon, z, hpolygonSub, hpolygonCard, _hpolygonStrong,
    hz, hstrongInsert⟩
  have hzData := Finset.mem_sdiff.mp hz
  have hzBlock : z ∈ block5 ∪ block5 ∪ block1 := hzData.1
  have hzSupport : z ∈ support := by
    rcases Finset.mem_union.mp hzBlock with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact block_sub block5 block5_mem hz
      · exact block_sub block5 block5_mem hz
    · exact block_sub block1 block1_mem hz
  have hzAmbient : z ∈ ambient := by
    simp [ambient, hzSupport]
  have hinsertSub : insert z polygon ⊆ ambient :=
    Finset.insert_subset hzAmbient (by simpa [ambient] using hpolygonSub)
  have hinsertCard : (insert z polygon).card = 6 := by
    rw [Finset.card_insert_of_notMem hzData.2, hpolygonCard]
  exact color_noStrongSix ⟨insert z polygon, hinsertSub, hinsertCard, hstrongInsert⟩

/-- The exact frozen universal statement, materialized as a proposition so
that a kernel-checked counterexample can refute it without adding an assumption. -/
def Fin15TripleOwnerResidueTwoCrossExteriorExtension : Prop :=
  ∀ (chi : TripleColoring 15) (hone : OneChangeOn chi Finset.univ)
    {support first second third : Finset (Fin 15)}
    {blocks : Finset (Finset (Fin 15))} {q r s x y : Fin 15},
    support.card = 7 →
    (∀ block ∈ blocks, block ⊆ support) →
    (∀ block ∈ blocks, block.card = 4) →
    (∀ pair : Finset (Fin 15), pair ⊆ support → pair.card = 2 →
      ∃! block : Finset (Fin 15), block ∈ blocks ∧ pair ⊆ support \ block) →
    first ∈ blocks → second ∈ blocks → third ∈ blocks →
    q ∈ Finset.univ \ support → r ∈ Finset.univ \ support →
    s ∈ Finset.univ \ support → q ≠ r → q ≠ s → r ≠ s →
    IsStrongPolygonSet chi (insert q first) →
    IsStrongPolygonSet chi (insert r second) →
    IsStrongPolygonSet chi (insert s third) →
    ¬first ⊆ (support.erase x).erase y →
    ¬second ⊆ (support.erase x).erase y →
    ¬third ⊆ (support.erase x).erase y →
    (∃ residue : Finset (Fin 15),
      residue ⊆ (support.erase x).erase y ∧ residue.card = 2 ∧
        IsStrongPolygonSet chi (insert q (insert r (insert s residue)))) →
    ∃ polygon : Finset (Fin 15), ∃ z : Fin 15,
      polygon ⊆ insert q (insert r (insert s support)) ∧
      polygon.card = 5 ∧ IsStrongPolygonSet chi polygon ∧
      z ∈ (first ∪ second ∪ third) \ polygon ∧
      IsStrongPolygonSet chi (insert z polygon)

/-- Kernel-checked refutation of the exact frozen helper contract. -/
theorem not_fin15TripleOwnerResidueTwoCrossExteriorExtension :
    ¬Fin15TripleOwnerResidueTwoCrossExteriorExtension := by
  intro hcontract
  apply no_crossExterior_extension
  exact hcontract color color_oneChange
    (support := support) (first := block5) (second := block5)
    (third := block1) (blocks := blocks) (q := q) (r := r) (s := s)
    (x := x) (y := y) support_card block_sub block_card
    fano_pair_complement block5_mem block5_mem block1_mem
    q_outside r_outside s_outside q_ne_r q_ne_s r_ne_s
    q_owner_strong r_owner_strong s_owner_strong first_killed
    second_killed third_killed
    ⟨residue, residue_sub, residue_card, triple_residue_strong⟩

end Fin15TripleCrossCounterexample
end ErdosSzekeres

end
