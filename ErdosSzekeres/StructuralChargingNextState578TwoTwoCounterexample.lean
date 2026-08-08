module

public import ErdosSzekeres.StructuralChargingNextState578TwoTwo
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# Counterexample to the five-internal-tail `2+2` gate

A deterministic bounded search found the tree below at its first trial.  This
file reconstructs it definitionally and kernel-checks every relevant property,
so the negative result does not depend on the search program.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578TwoTwoCounterexample

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def lowerTree : RankProfileCollision.DecompositionTree 9 :=
  .node
    (.node (.leaf 5) (.leaf 8))
    (.node (.leaf 6) (.leaf 2))

def upperTree : RankProfileCollision.DecompositionTree 9 :=
  .node
    (.node
      (.leaf 1)
      (.node
        (.node (.leaf 3) (.leaf 4))
        (.leaf 7)))
    (.leaf 0)

def tree : RankProfileCollision.DecompositionTree 9 :=
  .node lowerTree upperTree

def color : TripleColoring 9 := tree.coloring

def lower : Finset (Fin 9) := lowerTree.vertices

def upper : Finset (Fin 9) := upperTree.vertices

def support : Finset (Fin 9) := lower ∪ upper

def cap : Finset (Fin 9) := {2, 3, 4, 5}

def tails : Finset (Fin 9) := {0, 1, 6, 7, 8}

/-- Executable monochromaticity check for the concrete coloring. -/
def turnSetBool (s : Finset (Fin 9)) (turn : Turn) : Bool :=
  (List.finRange 9).all fun i ↦
    (List.finRange 9).all fun j ↦
      (List.finRange 9).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              decide (color ⟨i, j, k, hij, hjk⟩ = turn)
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 9)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 9, t.i ∈ s → t.j ∈ s → t.k ∈ s → color t = turn := by
  constructor
  · intro h t hi hj hk
    have hiCheck := (List.all_eq_true.mp h) t.i (List.mem_finRange t.i)
    have hjCheck := (List.all_eq_true.mp hiCheck) t.j (List.mem_finRange t.j)
    have hkCheck := (List.all_eq_true.mp hjCheck) t.k (List.mem_finRange t.k)
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
            · simp [hij, hjk, hi, hj, hk, h ⟨i, j, k, hij, hjk⟩ hi hj hk]
            · simp [hij, hjk, hi, hj, hk]
          · simp [hij, hjk, hi, hj]
        · simp [hij, hjk, hi]
      · simp [hij, hjk]
    · simp [hij]

theorem root_deep : HasDeepBelowSplit color lower upper := by
  have h := RankProfileCollision.DecompositionTree.node_split
    lowerTree upperTree (by decide)
  simpa [color, tree, lower, upper, lowerTree, upperTree,
    RankProfileCollision.DecompositionTree.vertices] using h

theorem support_eq_univ : support = Finset.univ := by decide

theorem cap_card : cap.card = 4 := by decide

theorem cap_isCapSet : IsCapSet color cap := by
  simpa [IsCapSet] using (turnSetBool_eq_true_iff cap .right).mp (by decide)

theorem cap_mem_witnesses : cap ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  exact ⟨by decide, cap_card, cap_isCapSet⟩

theorem cap_lower_card : (cap ∩ lower).card = 2 := by decide

theorem cap_upper_card : (cap ∩ upper).card = 2 := by decide

theorem lower_has_no_cup_six : ¬ContainsCupSet color lower 6 := by
  rintro ⟨cup, hsub, hcard, _hcup⟩
  have hcardLe := Finset.card_le_card hsub
  have hlowerCard : lower.card = 4 := by decide
  omega

theorem cap_is_terminal :
    ¬∃ inner, ∃ hinner : inner ∈ capWitnesses color support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) cap_mem_witnesses)) := by
  rintro ⟨inner, hinner, hinside⟩
  let hinnerNonempty := capWitness_nonempty_of_mem (by omega) hinner
  let hcapNonempty := capWitness_nonempty_of_mem (by omega) cap_mem_witnesses
  have hinnerSub : inner ⊆ Finset.Icc (inner.min' hinnerNonempty)
      (inner.max' hinnerNonempty) := by
    intro x hx
    exact Finset.mem_Icc.mpr
      ⟨Finset.min'_le inner x hx, Finset.le_max' inner x hx⟩
  have hcardLe := Finset.card_le_card hinnerSub
  rw [Fin.card_Icc] at hcardLe
  have hinnerCard : inner.card = 4 := (mem_capWitnesses.mp hinner).2.1
  have hinnerWidth : 3 ≤ (finsetSweepInterval inner hinnerNonempty).width := by
    change 3 ≤ (inner.max' hinnerNonempty).val - (inner.min' hinnerNonempty).val
    omega
  have hwidthLt := SweepInterval.width_lt_of_strictlyInside
    (finsetSweepInterval_lower_le_upper hinnerNonempty)
    (finsetSweepInterval_lower_le_upper hcapNonempty) hinside
  have hcapWidth : (finsetSweepInterval cap hcapNonempty).width = 3 := by
    decide
  rw [hcapWidth] at hwidthLt
  omega

theorem tails_subset_outer :
    tails ⊆ ((support \ openSweepSpanVertices support cap
      (capWitness_nonempty_of_mem (by omega) cap_mem_witnesses)) \ cap) := by
  decide

theorem tails_card : tails.card = 5 := by decide

theorem no_cap_five_bool :
    ∀ s : Finset (Fin 9), s.card = 5 → turnSetBool s .right = false := by
  decide

theorem no_cup_seven_bool :
    ∀ s : Finset (Fin 9), s.card = 7 → turnSetBool s .left = false := by
  decide

theorem no_strong_eight_bool :
    ∀ s : Finset (Fin 9), s.card = 8 →
      RankProfileCollision.strongPolygonSetBool color s = false := by
  decide

theorem no_cap_five : ¬ContainsCapSet color support 5 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cap_five_bool witness hcard
  have htrue : turnSetBool witness .right = true :=
    (turnSetBool_eq_true_iff witness .right).mpr (by
      simpa [IsCapSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_cup_seven : ¬ContainsCupSet color support 7 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cup_seven_bool witness hcard
  have htrue : turnSetBool witness .left = true :=
    (turnSetBool_eq_true_iff witness .left).mpr (by
      simpa [IsCupSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_strong_eight : ¬ContainsStrongPolygonSet color support 8 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_strong_eight_bool witness hcard
  have htrue :=
    (RankProfileCollision.strongPolygonSetBool_eq_true_iff color witness).2 hwitness
  rw [hfalse] at htrue
  contradiction

/-- Five internal outer tails do not close the terminal `2+2` branch, even at
the root of a recursively decomposable nine-vertex coloring. -/
theorem not_fiveInternalOuterTailGate578 : ¬FiveInternalOuterTailGate578 := by
  intro hgate
  have hout := hgate root_deep
    (by simpa [support] using cap_mem_witnesses)
    cap_lower_card cap_upper_card lower_has_no_cup_six
    (by simpa [support] using cap_is_terminal)
    (by simpa [support] using tails_subset_outer) tails_card
  exact hout.elim no_cap_five (fun h ↦ h.elim no_cup_seven no_strong_eight)

end StructuralChargingNextState578TwoTwoCounterexample
end ErdosSzekeres

end
