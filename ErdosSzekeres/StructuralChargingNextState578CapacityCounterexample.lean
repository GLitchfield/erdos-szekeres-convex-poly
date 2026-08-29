module

public import ErdosSzekeres.StructuralChargingNextState578Capacity
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# Native-checked candidate counterexample to two-tail multiplicity

A deterministic bounded search found this 17-vertex recursive coloring.  It
has no five-cap, seven-cup, or strong eight-set, but a terminal four-cap with
nine genuine outer tails has a disjoint secondary cap using only one tail.

The target-avoidance checks below use `native_decide` and therefore introduce
nonstandard generated axioms.  This module is retained as checked
computational evidence, not imported by the root library, and is not a
completed kernel-only formal result.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578CapacityCounterexample

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

open RankProfileCollision

def tree : RankProfileCollision.DecompositionTree 17 :=
  .node
    (.node
      (.node
        (.node (.leaf 14) (.node (.leaf 12) (.leaf 11)))
        (.node (.leaf 6) (.leaf 5)))
      (.node
        (.node
          (.node (.leaf 2) (.node (.leaf 9) (.leaf 7)))
          (.node (.leaf 1) (.leaf 3)))
        (.node
          (.node (.node (.leaf 15) (.leaf 0)) (.leaf 10))
          (.node (.leaf 16) (.leaf 4)))))
    (.node (.leaf 13) (.leaf 8))

/-- Local executable copy of the tree-support recursion.  Keeping it in this
module gives `native_decide` a direct compiled implementation. -/
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

def color : TripleColoring 17 := treeColoring tree

def support : Finset (Fin 17) := treeVertices tree

def terminal : Finset (Fin 17) := {7, 8, 13, 14}

def tails : Finset (Fin 17) := {0, 1, 2, 3, 4, 5, 6, 15, 16}

def secondary : Finset (Fin 17) := {5, 9, 10, 11}

/-- Executable equality on turns, kept local so native certificate evaluation
does not depend on an external generated instance. -/
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
def turnSetBool (s : Finset (Fin 17)) (turn : Turn) : Bool :=
  (List.finRange 17).all fun i ↦
    (List.finRange 17).all fun j ↦
      (List.finRange 17).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              turnEq (color ⟨i, j, k, hij, hjk⟩) turn
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 17)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 17, t.i ∈ s → t.j ∈ s → t.k ∈ s →
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

/-- Check the color of the unique ordered triple in a three-set. -/
def tripleSetBool (s : Finset (Fin 17)) (turn : Turn) : Bool :=
  if hcard : s.card = 3 then
    let e := s.orderEmbOfFin hcard
    turnEq (color ⟨e 0, e 1, e 2,
      e.strictMono (by decide), e.strictMono (by decide)⟩) turn
  else false

/-- Efficient monochromaticity checker using only three-subsets. -/
def monochromaticSetCheck (s : Finset (Fin 17)) (turn : Turn) : ℕ :=
  ∏ triple ∈ s.powersetCard 3,
    if tripleSetBool triple turn then 1 else 0

theorem monochromaticSetCheck_eq_one_of (s : Finset (Fin 17)) (turn : Turn)
    (hmono : ∀ t : OrderedTriple 17,
      t.i ∈ s → t.j ∈ s → t.k ∈ s → color t = turn) :
    monochromaticSetCheck s turn = 1 := by
  apply Finset.prod_eq_one
  intro triple htriple
  have hpower := Finset.mem_powersetCard.mp htriple
  let e := triple.orderEmbOfFin hpower.2
  have hcolor := hmono ⟨e 0, e 1, e 2,
      e.strictMono (by decide), e.strictMono (by decide)⟩
    (hpower.1 (triple.orderEmbOfFin_mem hpower.2 0))
    (hpower.1 (triple.orderEmbOfFin_mem hpower.2 1))
    (hpower.1 (triple.orderEmbOfFin_mem hpower.2 2))
  have hcolor' : color ⟨(triple.orderEmbOfFin hpower.2) 0,
      (triple.orderEmbOfFin hpower.2) 1,
      (triple.orderEmbOfFin hpower.2) 2,
      (triple.orderEmbOfFin hpower.2).strictMono (by decide),
      (triple.orderEmbOfFin hpower.2).strictMono (by decide)⟩ = turn := by
    simpa [e] using hcolor
  simp [tripleSetBool, hpower.2, hcolor', turnEq_self]

/-- Check the strong-polygon equations on the unique ordered four-tuple in a
four-set. -/
def strongFourBool (s : Finset (Fin 17)) : Bool :=
  if hcard : s.card = 4 then
    let e := s.orderEmbOfFin hcard
    turnEq
      (color ⟨e 0, e 1, e 2,
          e.strictMono (by decide), e.strictMono (by decide)⟩)
      (color ⟨e 0, e 1, e 3,
          e.strictMono (by decide), e.strictMono (by decide)⟩) &&
      turnEq
        (color ⟨e 0, e 2, e 3,
          e.strictMono (by decide), e.strictMono (by decide)⟩)
        (color ⟨e 1, e 2, e 3,
          e.strictMono (by decide), e.strictMono (by decide)⟩)
  else false

/-- Efficient strong-polygon checker using only four-subsets. -/
def strongSetCheck (s : Finset (Fin 17)) : ℕ :=
  ∏ four ∈ s.powersetCard 4, if strongFourBool four then 1 else 0

theorem strongSetCheck_eq_one_of (s : Finset (Fin 17))
    (hstrong : IsStrongPolygonSet color s) : strongSetCheck s = 1 := by
  apply Finset.prod_eq_one
  intro four hfour
  have hpower := Finset.mem_powersetCard.mp hfour
  let e := four.orderEmbOfFin hpower.2
  have hresult := hstrong
    (e.strictMono (by decide)) (e.strictMono (by decide))
    (e.strictMono (by decide))
    (hpower.1 (four.orderEmbOfFin_mem hpower.2 0))
    (hpower.1 (four.orderEmbOfFin_mem hpower.2 1))
    (hpower.1 (four.orderEmbOfFin_mem hpower.2 2))
    (hpower.1 (four.orderEmbOfFin_mem hpower.2 3))
  have hresult' :
      color ⟨(four.orderEmbOfFin hpower.2) 0,
          (four.orderEmbOfFin hpower.2) 1,
          (four.orderEmbOfFin hpower.2) 2,
          (four.orderEmbOfFin hpower.2).strictMono (by decide),
          (four.orderEmbOfFin hpower.2).strictMono (by decide)⟩ =
        color ⟨(four.orderEmbOfFin hpower.2) 0,
          (four.orderEmbOfFin hpower.2) 1,
          (four.orderEmbOfFin hpower.2) 3,
          (four.orderEmbOfFin hpower.2).strictMono (by decide),
          (four.orderEmbOfFin hpower.2).strictMono (by decide)⟩ ∧
      color ⟨(four.orderEmbOfFin hpower.2) 0,
          (four.orderEmbOfFin hpower.2) 2,
          (four.orderEmbOfFin hpower.2) 3,
          (four.orderEmbOfFin hpower.2).strictMono (by decide),
          (four.orderEmbOfFin hpower.2).strictMono (by decide)⟩ =
        color ⟨(four.orderEmbOfFin hpower.2) 1,
          (four.orderEmbOfFin hpower.2) 2,
          (four.orderEmbOfFin hpower.2) 3,
          (four.orderEmbOfFin hpower.2).strictMono (by decide),
          (four.orderEmbOfFin hpower.2).strictMono (by decide)⟩ := by
    simpa [e] using hresult
  simp [strongFourBool, hpower.2, hresult', turnEq_self]

theorem support_eq_univ : support = Finset.univ := by decide

theorem terminal_mem_witnesses : terminal ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff terminal .right).mp (by decide)

theorem secondary_mem_witnesses : secondary ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff secondary .right).mp (by decide)

theorem terminal_secondary_disjoint : Disjoint terminal secondary := by decide

theorem tails_eq_outer :
    tails = (support \ openSweepSpanVertices support terminal
      (capWitness_nonempty_of_mem (by omega) terminal_mem_witnesses)) \
        terminal := by
  decide

theorem tails_card : tails.card = 9 := by decide

theorem secondary_tail_card : (secondary ∩ tails).card = 1 := by decide

theorem no_strictly_inner_cap_bool :
    ∀ s : Finset (Fin 17), s.card = 4 →
      s ⊆ Finset.Icc 7 14 →
      (s ⊆ Finset.Icc 8 14 ∨ s ⊆ Finset.Icc 7 13) →
      turnSetBool s .right = false := by
  native_decide

theorem terminal_is_terminal :
    ¬∃ inner, ∃ hinner : inner ∈ capWitnesses color support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval terminal
        (capWitness_nonempty_of_mem (by omega) terminal_mem_witnesses)) := by
  rintro ⟨inner, hinner, hinside⟩
  have hinnerData := mem_capWitnesses.mp hinner
  let hinnerNonempty := capWitness_nonempty_of_mem (by omega) hinner
  have hbounds :
      7 ≤ (inner.min' hinnerNonempty).val ∧
      (inner.max' hinnerNonempty).val ≤ 14 ∧
      (7 < (inner.min' hinnerNonempty).val ∨
        (inner.max' hinnerNonempty).val < 14) := by
    simpa [SweepInterval.StrictlyInside, finsetSweepInterval, terminal] using
      hinside
  have hIcc : inner ⊆ Finset.Icc 7 14 := by
    intro x hx
    rw [Finset.mem_Icc]
    have hmin := Finset.min'_le inner x hx
    have hmax := Finset.le_max' inner x hx
    exact ⟨by omega, by omega⟩
  have hstrict : inner ⊆ Finset.Icc 8 14 ∨
      inner ⊆ Finset.Icc 7 13 := by
    rcases hbounds.2.2 with hleft | hright
    · left
      intro x hx
      rw [Finset.mem_Icc]
      have hmin := Finset.min'_le inner x hx
      have hmax := Finset.le_max' inner x hx
      exact ⟨by omega, by omega⟩
    · right
      intro x hx
      rw [Finset.mem_Icc]
      have hmin := Finset.min'_le inner x hx
      have hmax := Finset.le_max' inner x hx
      exact ⟨by omega, by omega⟩
  have hfalse := no_strictly_inner_cap_bool inner
    hinnerData.2.1 hIcc hstrict
  have htrue : turnSetBool inner .right = true :=
    (turnSetBool_eq_true_iff inner .right).mpr (by
      simpa [IsCapSet] using hinnerData.2.2)
  rw [hfalse] at htrue
  contradiction

def noCapFiveCheck : ℕ :=
  ∏ s ∈ (Finset.univ : Finset (Fin 17)).powersetCard 5,
    if monochromaticSetCheck s .right = 0 then 1 else 0

def noCupSevenCheck : ℕ :=
  ∏ s ∈ (Finset.univ : Finset (Fin 17)).powersetCard 7,
    if monochromaticSetCheck s .left = 0 then 1 else 0

def noStrongEightCheck : ℕ :=
  ∏ s ∈ (Finset.univ : Finset (Fin 17)).powersetCard 8,
    if strongSetCheck s = 0 then 1 else 0

theorem noCapFiveCheck_eq_one : noCapFiveCheck = 1 := by native_decide

theorem noCupSevenCheck_eq_one : noCupSevenCheck = 1 := by native_decide

theorem noStrongEightCheck_eq_one : noStrongEightCheck = 1 := by native_decide

theorem no_cap_five_fast (s : Finset (Fin 17)) (hcard : s.card = 5) :
    monochromaticSetCheck s .right = 0 := by
  have hmem : s ∈ Finset.univ.powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  have hterm := (Finset.prod_eq_one_iff.mp noCapFiveCheck_eq_one) s hmem
  simpa using hterm

theorem no_cup_seven_fast (s : Finset (Fin 17)) (hcard : s.card = 7) :
    monochromaticSetCheck s .left = 0 := by
  have hmem : s ∈ Finset.univ.powersetCard 7 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  have hterm := (Finset.prod_eq_one_iff.mp noCupSevenCheck_eq_one) s hmem
  simpa using hterm

theorem no_strong_eight_fast (s : Finset (Fin 17)) (hcard : s.card = 8) :
    strongSetCheck s = 0 := by
  have hmem : s ∈ Finset.univ.powersetCard 8 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  have hterm := (Finset.prod_eq_one_iff.mp noStrongEightCheck_eq_one) s hmem
  simpa using hterm

theorem no_cap_five : ¬ContainsCapSet color support 5 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cap_five_fast witness hcard
  have htrue : monochromaticSetCheck witness .right = 1 :=
    monochromaticSetCheck_eq_one_of witness .right (by
      simpa [IsCapSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_cup_seven : ¬ContainsCupSet color support 7 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_cup_seven_fast witness hcard
  have htrue : monochromaticSetCheck witness .left = 1 :=
    monochromaticSetCheck_eq_one_of witness .left (by
      simpa [IsCupSet] using hwitness)
  rw [hfalse] at htrue
  contradiction

theorem no_strong_eight : ¬ContainsStrongPolygonSet color support 8 := by
  rintro ⟨witness, _, hcard, hwitness⟩
  have hfalse := no_strong_eight_fast witness hcard
  have htrue := strongSetCheck_eq_one_of witness hwitness
  rw [hfalse] at htrue
  contradiction

/-- Nine terminal tails do not force every disjoint secondary cap to consume
two tails, even under all three target-avoidance assumptions. -/
theorem not_terminalNineTailSecondaryMultiplicityGate578 :
    ¬TerminalNineTailSecondaryMultiplicityGate578 := by
  intro hgate
  have hout := hgate (secondary := secondary)
    terminal_mem_witnesses terminal_is_terminal
    no_cap_five no_cup_seven no_strong_eight
  rw [← tails_eq_outer] at hout
  have htailNine : 9 ≤ tails.card := by rw [tails_card]
  have htwo := hout htailNine secondary_mem_witnesses
    terminal_secondary_disjoint
  rw [secondary_tail_card] at htwo
  omega

end StructuralChargingNextState578CapacityCounterexample
end ErdosSzekeres

end
