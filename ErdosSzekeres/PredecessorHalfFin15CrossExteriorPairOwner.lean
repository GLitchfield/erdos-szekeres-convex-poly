module

public import ErdosSzekeres.PredecessorHalfFin15CrossExterior

@[expose] public section

/-!
# Exact counterexample to the frozen pair-owner cross-exterior helper

The frozen helper retains only the three killed-block propositions.  Those
propositions do not imply that either erased point kills both owner blocks.
This file gives a finite `OneChangeOn` coloring witnessing that gap and proves,
inside Lean, that every premise of the frozen helper holds while its conclusion
does not.
-/

namespace ErdosSzekeres
namespace Fin15PairOwnerCounterexample

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Codes of the right-colored triples in the ten-vertex core. -/
def rightCodes : Finset Nat :=
  {12, 13, 14, 15, 16, 17, 18, 25, 35, 45, 46, 47, 48, 78,
   235, 236, 245, 246, 247, 248, 278, 345, 346, 347, 348, 378,
   578, 678, 679, 689}

/-- All triples outside the encoded ten-vertex core are left. -/
def coloring : TripleColoring 15 := fun t =>
  if 100 * t.i.val + 10 * t.j.val + t.k.val ∈ rightCodes then
    Turn.right
  else
    Turn.left

def support : Finset (Fin 15) := {0, 1, 2, 3, 4, 5, 6}

def block0 : Finset (Fin 15) := {3, 4, 5, 6}
def block1 : Finset (Fin 15) := {1, 2, 5, 6}
def block2 : Finset (Fin 15) := {1, 2, 3, 4}
def block3 : Finset (Fin 15) := {0, 2, 4, 6}
def block4 : Finset (Fin 15) := {0, 2, 3, 5}
def block5 : Finset (Fin 15) := {0, 1, 4, 5}
def block6 : Finset (Fin 15) := {0, 1, 3, 6}

/-- The seven Fano-complement blocks, with one duplicate in the eighth slot. -/
def indexedBlock : Fin 8 → Finset (Fin 15) :=
  ![block0, block1, block2, block3, block4, block5, block6, block6]

def blocks : Finset (Finset (Fin 15)) := Finset.univ.image indexedBlock

def first : Finset (Fin 15) := block0
def second : Finset (Fin 15) := block1
def third : Finset (Fin 15) := block2
def residue : Finset (Fin 15) := {0, 5, 6}

def a : Fin 15 := 7
def b : Fin 15 := 8
def c : Fin 15 := 9
def x : Fin 15 := 3
def y : Fin 15 := 1
def ambient : Finset (Fin 15) := insert a (insert b (insert c support))

/-- Executable checker for the strong-polygon law on one finite set. -/
def strongPolygonSetBool (chi : TripleColoring 15)
    (polygon : Finset (Fin 15)) : Bool :=
  (List.finRange 15).all fun i =>
    (List.finRange 15).all fun j =>
      (List.finRange 15).all fun k =>
        (List.finRange 15).all fun l =>
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
    Decidable (ContainsStrongPolygonSet coloring ambient 6) := by
  unfold ContainsStrongPolygonSet
  infer_instance

/-- The ten active vertices contain no strong six-set. -/
theorem coloring_noStrongSix :
    ¬ContainsStrongPolygonSet coloring ambient 6 := by
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

theorem turnSequenceAllowedBool_eq_true_iff (u v w t : Turn) :
    turnSequenceAllowedBool u v w t = true ↔
      TurnSequenceAllowed u v w t := by
  cases u <;> cases v <;> cases w <;> cases t <;>
    simp [turnSequenceAllowedBool, TurnSequenceAllowed]

/-- Executable checker for the one-change law on all fifteen vertices. -/
def oneChangeOnUnivBool (chi : TripleColoring 15) : Bool :=
  (List.finRange 15).all fun i =>
    (List.finRange 15).all fun j =>
      (List.finRange 15).all fun k =>
        (List.finRange 15).all fun l =>
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
        · simp [hij, hjk, hkl]
      · simp [hij, hjk]
    · simp [hij]

theorem coloring_oneChange : OneChangeOn coloring Finset.univ := by
  apply (oneChangeOnUnivBool_eq_true_iff coloring).mp
  decide

theorem support_card : support.card = 7 := by decide

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

theorem blocks_card : blocks.card = 7 := by decide

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

theorem fano_blocks :
    ∀ pair : Finset (Fin 15), pair ⊆ support → pair.card = 2 →
      ∃! block : Finset (Fin 15), block ∈ blocks ∧ pair ⊆ support \ block := by
  have hclassification := eight_fourBlock_family_fano_classification
    support indexedBlock support_card indexedBlock_sub indexedBlock_card
      indexedBlock_small_inter
  exact hclassification.2.1 blocks_card

theorem first_mem : first ∈ blocks := by decide
theorem second_mem : second ∈ blocks := by decide
theorem third_mem : third ∈ blocks := by decide

theorem a_outside : a ∈ Finset.univ \ support := by decide
theorem b_outside : b ∈ Finset.univ \ support := by decide
theorem c_outside : c ∈ Finset.univ \ support := by decide
theorem a_ne_b : a ≠ b := by decide
theorem a_ne_c : a ≠ c := by decide
theorem b_ne_c : b ≠ c := by decide

theorem a_owner_strong : IsStrongPolygonSet coloring (insert a first) := by
  apply (strongPolygonSetBool_eq_true_iff coloring _).mp
  decide

theorem b_owner_strong : IsStrongPolygonSet coloring (insert b second) := by
  apply (strongPolygonSetBool_eq_true_iff coloring _).mp
  decide

theorem c_owner_strong : IsStrongPolygonSet coloring (insert c third) := by
  apply (strongPolygonSetBool_eq_true_iff coloring _).mp
  decide

theorem first_killed : ¬first ⊆ (support.erase x).erase y := by decide
theorem second_killed : ¬second ⊆ (support.erase x).erase y := by decide
theorem third_killed : ¬third ⊆ (support.erase x).erase y := by decide

theorem residue_sub : residue ⊆ (support.erase x).erase y := by decide
theorem residue_card : residue.card = 3 := by decide
theorem pair_residue_strong :
    IsStrongPolygonSet coloring (insert a (insert b residue)) := by
  apply (strongPolygonSetBool_eq_true_iff coloring _).mp
  decide

/-- No conclusion of the frozen helper exists for the concrete premises. -/
theorem no_crossExterior_extension :
    ¬∃ polygon : Finset (Fin 15), ∃ z : Fin 15,
      polygon ⊆ insert a (insert b (insert c support)) ∧
      polygon.card = 5 ∧
      IsStrongPolygonSet coloring polygon ∧
      z ∈ (first ∪ second ∪ third) \ polygon ∧
      IsStrongPolygonSet coloring (insert z polygon) := by
  rintro ⟨polygon, z, hpolygonSub, hpolygonCard, _hpolygonStrong,
    hz, hstrongInsert⟩
  have hzData := Finset.mem_sdiff.mp hz
  have hzBlock : z ∈ first ∪ second ∪ third := hzData.1
  have hzSupport : z ∈ support := by
    rcases Finset.mem_union.mp hzBlock with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact block_sub first first_mem hz
      · exact block_sub second second_mem hz
    · exact block_sub third third_mem hz
  have hzAmbient : z ∈ ambient := by
    simp [ambient, hzSupport]
  have hinsertSub : insert z polygon ⊆ ambient :=
    Finset.insert_subset hzAmbient (by simpa [ambient] using hpolygonSub)
  have hinsertCard : (insert z polygon).card = 6 := by
    rw [Finset.card_insert_of_notMem hzData.2, hpolygonCard]
  exact coloring_noStrongSix
    ⟨insert z polygon, hinsertSub, hinsertCard, hstrongInsert⟩

/-- The exact proposition asserted by the frozen Lane 2 helper. -/
def FrozenPairOwnerStatement : Prop :=
  ∀ (chi : TripleColoring 15), OneChangeOn chi Finset.univ →
    ∀ {support first second third : Finset (Fin 15)}
      {blocks : Finset (Finset (Fin 15))} {a b c x y : Fin 15},
    support.card = 7 →
    (∀ block ∈ blocks, block ⊆ support) →
    (∀ block ∈ blocks, block.card = 4) →
    (∀ pair : Finset (Fin 15), pair ⊆ support → pair.card = 2 →
      ∃! block : Finset (Fin 15), block ∈ blocks ∧ pair ⊆ support \ block) →
    first ∈ blocks → second ∈ blocks → third ∈ blocks →
    a ∈ Finset.univ \ support → b ∈ Finset.univ \ support →
    c ∈ Finset.univ \ support → a ≠ b → a ≠ c → b ≠ c →
    IsStrongPolygonSet chi (insert a first) →
    IsStrongPolygonSet chi (insert b second) →
    IsStrongPolygonSet chi (insert c third) →
    ¬first ⊆ (support.erase x).erase y →
    ¬second ⊆ (support.erase x).erase y →
    ¬third ⊆ (support.erase x).erase y →
    (∃ residue : Finset (Fin 15),
      residue ⊆ (support.erase x).erase y ∧ residue.card = 3 ∧
        IsStrongPolygonSet chi (insert a (insert b residue))) →
    ∃ polygon : Finset (Fin 15), ∃ z : Fin 15,
      polygon ⊆ insert a (insert b (insert c support)) ∧
      polygon.card = 5 ∧ IsStrongPolygonSet chi polygon ∧
      z ∈ (first ∪ second ∪ third) \ polygon ∧
      IsStrongPolygonSet chi (insert z polygon)

/-- A kernel-checked refutation of the exact frozen helper proposition. -/
theorem not_frozenPairOwnerStatement : ¬FrozenPairOwnerStatement := by
  intro hcontract
  apply no_crossExterior_extension
  exact hcontract coloring coloring_oneChange
    (support := support) (first := first) (second := second) (third := third)
    (blocks := blocks) (a := a) (b := b) (c := c) (x := x) (y := y)
    support_card block_sub block_card fano_blocks first_mem second_mem third_mem
    a_outside b_outside c_outside a_ne_b a_ne_c b_ne_c
    a_owner_strong b_owner_strong c_owner_strong first_killed second_killed
    third_killed ⟨residue, residue_sub, residue_card, pair_residue_strong⟩

end Fin15PairOwnerCounterexample
end ErdosSzekeres

end
