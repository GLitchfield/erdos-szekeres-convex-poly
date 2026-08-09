module

public import ErdosSzekeres.StructuralChargingNextState578PrivateCapTrace
public import ErdosSzekeres.RankProfileCollision

@[expose] public section

/-!
# Eight-vertex obstruction to single-private-cap trace closure

The recursively decomposable coloring below has a terminal four-cap and a
disjoint private four-cap.  The private cap first peels at an upper-directed
terminal-path step; its owner then exits at a lower-directed step.  No two
private-cap vertices occupy one lower-sibling bucket.  The coloring avoids the
state-578 targets, so a trace theorem treating private caps independently
cannot close the obstruction.  The example does not have the six-owner or
`32/23` density hypotheses.
-/

namespace ErdosSzekeres
namespace StructuralChargingNextState578PrivateCapTraceCounterexample

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def bRankTree : RankProfileCollision.DecompositionTree 8 :=
  .node (.node (.leaf 7) (.leaf 3)) (.leaf 2)

def dRankTree : RankProfileCollision.DecompositionTree 8 :=
  .node (.node (.leaf 4) (.leaf 0)) (.leaf 6)

def eRankTree : RankProfileCollision.DecompositionTree 8 :=
  .node bRankTree dRankTree

def fRankTree : RankProfileCollision.DecompositionTree 8 :=
  .node eRankTree (.leaf 1)

def rankTree : RankProfileCollision.DecompositionTree 8 :=
  .node (.leaf 5) fRankTree

def color : TripleColoring 8 := rankTree.coloring

def eLower : Finset (Fin 8) := bRankTree.vertices
def eUpper : Finset (Fin 8) := dRankTree.vertices
def eSupport : Finset (Fin 8) := eLower ∪ eUpper
def fUpper : Finset (Fin 8) := {1}
def fSupport : Finset (Fin 8) := eSupport ∪ fUpper
def rootLower : Finset (Fin 8) := {5}
def support : Finset (Fin 8) := rootLower ∪ fSupport

def terminal : Finset (Fin 8) := {3, 4, 6, 7}
def privateCap : Finset (Fin 8) := {0, 1, 2, 5}
def marked : Finset (Fin 8) := {1}
def capFor (_ : Fin 8) : Finset (Fin 8) := privateCap
def path : List Bool := [true, false]

/-- Executable monochromaticity check for the concrete coloring. -/
def turnSetBool (s : Finset (Fin 8)) (turn : Turn) : Bool :=
  (List.finRange 8).all fun i ↦
    (List.finRange 8).all fun j ↦
      (List.finRange 8).all fun k ↦
        if hij : i < j then
          if hjk : j < k then
            if i ∈ s ∧ j ∈ s ∧ k ∈ s then
              decide (color ⟨i, j, k, hij, hjk⟩ = turn)
            else true
          else true
        else true

theorem turnSetBool_eq_true_iff (s : Finset (Fin 8)) (turn : Turn) :
    turnSetBool s turn = true ↔
      ∀ t : OrderedTriple 8, t.i ∈ s → t.j ∈ s → t.k ∈ s →
        color t = turn := by
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
            · simp [hij, hjk, hi, hj, hk,
                h ⟨i, j, k, hij, hjk⟩ hi hj hk]
            · simp [hij, hjk, hi, hj, hk]
          · simp [hij, hjk, hi, hj]
        · simp [hij, hjk, hi]
      · simp [hij, hjk]
    · simp [hij]

theorem support_eq_univ : support = Finset.univ := by decide

theorem rankTree_wellFormed : rankTree.WellFormed := by
  simp [rankTree, fRankTree, eRankTree, bRankTree, dRankTree,
    RankProfileCollision.DecompositionTree.WellFormed,
    RankProfileCollision.DecompositionTree.vertices]

theorem support_decomposable : IsDecomposableOn color support := by
  have h := rankTree.decomposableOn rankTree_wellFormed
  simpa [color, support, rootLower, fSupport, fUpper, eSupport, eLower,
    eUpper, rankTree, fRankTree, eRankTree,
    RankProfileCollision.DecompositionTree.vertices] using h

theorem terminal_mem_witnesses :
    terminal ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff terminal .right).mp (by decide)

theorem privateCap_mem_witnesses :
    privateCap ∈ capWitnesses color support 4 := by
  apply mem_capWitnesses.mpr
  refine ⟨by decide, by decide, ?_⟩
  simpa [IsCapSet] using
    (turnSetBool_eq_true_iff privateCap .right).mp (by decide)

theorem no_cap_five_bool :
    ∀ s : Finset (Fin 8), s.card = 5 →
      turnSetBool s .right = false := by decide

theorem no_cup_seven_bool :
    ∀ s : Finset (Fin 8), s.card = 7 →
      turnSetBool s .left = false := by decide

theorem no_strong_eight_bool :
    ∀ s : Finset (Fin 8), s.card = 8 →
      RankProfileCollision.strongPolygonSetBool color s = false := by decide

theorem no_strictly_inner_cap_bool :
    ∀ s : Finset (Fin 8), s.card = 4 →
      s ⊆ Finset.Icc 3 7 →
      (s ⊆ Finset.Icc 4 7 ∨ s ⊆ Finset.Icc 3 6) →
      turnSetBool s .right = false := by decide

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
    (RankProfileCollision.strongPolygonSetBool_eq_true_iff color witness).2
      hwitness
  rw [hfalse] at htrue
  contradiction

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
      3 ≤ (inner.min' hinnerNonempty).val ∧
      (inner.max' hinnerNonempty).val ≤ 7 ∧
      (3 < (inner.min' hinnerNonempty).val ∨
        (inner.max' hinnerNonempty).val < 7) := by
    simpa [SweepInterval.StrictlyInside, finsetSweepInterval, terminal] using
      hinside
  have hIcc : inner ⊆ Finset.Icc 3 7 := by
    intro x hx
    rw [Finset.mem_Icc]
    have hmin := Finset.min'_le inner x hx
    have hmax := Finset.le_max' inner x hx
    exact ⟨by omega, by omega⟩
  have hstrict : inner ⊆ Finset.Icc 4 7 ∨
      inner ⊆ Finset.Icc 3 6 := by
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

/-- A deep split is unchanged when the ambient coloring agrees on all triples
inside the split support. -/
theorem deepBelowSplit_of_eqOn
    {χ ψ : TripleColoring 8} {lower upper : Finset (Fin 8)}
    (hdeep : HasDeepBelowSplit ψ lower upper)
    (heq : ∀ t : OrderedTriple 8,
      t.i ∈ lower ∪ upper → t.j ∈ lower ∪ upper →
      t.k ∈ lower ∪ upper → χ t = ψ t) :
    HasDeepBelowSplit χ lower upper := by
  refine ⟨hdeep.disjoint, ?_⟩
  intro t hi hj hk hnotLower hnotUpper
  rw [heq t hi hj hk]
  exact hdeep.crossing t hi hj hk hnotLower hnotUpper

theorem color_agrees_fRankTree :
    ∀ t : OrderedTriple 8,
      t.i ∈ fSupport → t.j ∈ fSupport → t.k ∈ fSupport →
        color t = fRankTree.coloring t := by
  intro t hi hj hk
  have hdis : Disjoint rootLower fSupport := by decide
  have hni : t.i ∉ rootLower := fun hroot =>
    (Finset.disjoint_left.mp hdis) hroot hi
  have hni5 : t.i ≠ 5 := by simpa [rootLower] using hni
  have hfVertices : fRankTree.vertices = fSupport := by decide
  have hiF : t.i ∈ fRankTree.vertices := by rw [hfVertices]; exact hi
  have hjF : t.j ∈ fRankTree.vertices := by rw [hfVertices]; exact hj
  have hkF : t.k ∈ fRankTree.vertices := by rw [hfVertices]; exact hk
  simp [color, rankTree, hni5, hiF, hjF, hkF,
    RankProfileCollision.DecompositionTree.coloring,
    RankProfileCollision.DecompositionTree.vertices]

theorem color_agrees_eRankTree :
    ∀ t : OrderedTriple 8,
      t.i ∈ eSupport → t.j ∈ eSupport → t.k ∈ eSupport →
        color t = eRankTree.coloring t := by
  intro t hi hj hk
  have hdis : Disjoint rootLower eSupport := by decide
  have hni : t.i ∉ rootLower := fun hroot =>
    (Finset.disjoint_left.mp hdis) hroot hi
  have hni5 : t.i ≠ 5 := by simpa [rootLower] using hni
  have hfVertices : fRankTree.vertices = fSupport := by decide
  have heVertices : eRankTree.vertices = eSupport := by decide
  have hiF : t.i ∈ fRankTree.vertices := by
    rw [hfVertices]
    exact Finset.mem_union_left fUpper hi
  have hjF : t.j ∈ fRankTree.vertices := by
    rw [hfVertices]
    exact Finset.mem_union_left fUpper hj
  have hkF : t.k ∈ fRankTree.vertices := by
    rw [hfVertices]
    exact Finset.mem_union_left fUpper hk
  have hiE : t.i ∈ eRankTree.vertices := by rw [heVertices]; exact hi
  have hjE : t.j ∈ eRankTree.vertices := by rw [heVertices]; exact hj
  have hkE : t.k ∈ eRankTree.vertices := by rw [heVertices]; exact hk
  simp [color, rankTree, fRankTree, hni5, hiE, hjE, hkE,
    RankProfileCollision.DecompositionTree.coloring,
    RankProfileCollision.DecompositionTree.vertices]

theorem root_deep : HasDeepBelowSplit color rootLower fSupport := by
  have h := RankProfileCollision.DecompositionTree.node_split
    (.leaf 5) fRankTree (by decide)
  simpa [color, rankTree, rootLower, fSupport, fUpper, eSupport, eLower,
    eUpper, fRankTree, eRankTree,
    RankProfileCollision.DecompositionTree.vertices] using h

theorem f_deep : HasDeepBelowSplit color eSupport fUpper := by
  have h := RankProfileCollision.DecompositionTree.node_split
    eRankTree (.leaf 1) (by decide)
  apply deepBelowSplit_of_eqOn h
  intro t hi hj hk
  exact color_agrees_fRankTree t hi hj hk

theorem e_deep : HasDeepBelowSplit color eLower eUpper := by
  have h := RankProfileCollision.DecompositionTree.node_split
    bRankTree dRankTree (by decide)
  apply deepBelowSplit_of_eqOn h
  intro t hi hj hk
  exact color_agrees_eRankTree t hi hj hk

theorem eLower_decomposable : IsDecomposableOn color eLower := by
  exact support_decomposable.subset (by decide) (by decide)

theorem eUpper_decomposable : IsDecomposableOn color eUpper := by
  exact support_decomposable.subset (by decide) (by decide)

noncomputable def eLowerTree : DecompositionTree color eLower :=
  Classical.choice
    (DecompositionTree.exists_of_isDecomposableOn eLower_decomposable)

noncomputable def eUpperTree : DecompositionTree color eUpper :=
  Classical.choice
    (DecompositionTree.exists_of_isDecomposableOn eUpper_decomposable)

noncomputable def eTree : DecompositionTree color eSupport := by
  exact .split eLowerTree eUpperTree e_deep

def oneTree : DecompositionTree color fUpper := by
  simpa [fUpper] using (DecompositionTree.singleton (χ := color) (1 : Fin 8))

noncomputable def fTree : DecompositionTree color fSupport := by
  exact .split eTree oneTree f_deep

def fiveTree : DecompositionTree color rootLower := by
  simpa [rootLower] using
    (DecompositionTree.singleton (χ := color) (5 : Fin 8))

noncomputable def tree : DecompositionTree color support := by
  exact .split fiveTree fTree root_deep

def node : DecompositionSplit color := ⟨eLower, eUpper, e_deep⟩

theorem path_lookup : tree.splitAtPath path = some node := by
  simp [tree, fTree, eTree, path, node, DecompositionTree.splitAtPath]

theorem terminal_lowest_path :
    DecompositionTree.IsLowestSeparatingPath terminal tree path := by
  apply DecompositionTree.IsLowestSeparatingPath.upper
  · decide
  · decide
  apply DecompositionTree.IsLowestSeparatingPath.lower
  · decide
  exact DecompositionTree.IsLowestSeparatingPath.root
    (by decide) (by decide) (by decide)

theorem owner_false_exit :
    DecompositionTree.FirstExitAlongPath terminal (1 : Fin 8)
      tree path false := by
  apply DecompositionTree.FirstExitAlongPath.upperBelow
      fiveTree fTree root_deep
  · decide
  · decide
  exact DecompositionTree.FirstExitAlongPath.lowerHere
    eTree oneTree f_deep (by decide) (by decide)

theorem privateCap_true_first_escape :
    DecompositionTree.FirstSetEscapeAlongPath privateCap tree path true := by
  exact DecompositionTree.FirstSetEscapeAlongPath.upperHere
    fiveTree fTree root_deep (by decide) (by decide)

theorem private_assignment :
    IsPrivateFourCapAssignment color support terminal marked capFor := by
  intro x hx
  have hxOne : x = 1 := by simpa [marked] using hx
  subst x
  exact ⟨privateCap_mem_witnesses, by decide, by decide, by decide⟩

theorem no_privateCap_lowerSiblingBucket_collision :
    ¬∃ bucket, bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧
      ∃ y ∈ privateCap, ∃ z ∈ privateCap,
        y ≠ z ∧ y ∈ bucket ∧ z ∈ bucket := by
  simp [tree, fTree, eTree, path, privateCap, fUpper,
    DecompositionTree.lowerSiblingSupportsAlongPath,
    DecompositionTree.supportSet]

/-- A kernel-checked target-free example realizes the collision-free branch:
the whole private cap first peels at a true step and its owner exits false one
level later.  Thus independent single-cap tracing is not a closure theorem. -/
theorem collision_free_upper_then_lower_privateCap_trace_is_target_free :
    IsDecomposableOn color support ∧
    ¬ContainsCapSet color support 5 ∧
    ¬ContainsCupSet color support 7 ∧
    ¬ContainsStrongPolygonSet color support 8 ∧
    terminal ∈ capWitnesses color support 4 ∧
    (¬∃ inner, ∃ hinner : inner ∈ capWitnesses color support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval terminal
        (capWitness_nonempty_of_mem (by omega) terminal_mem_witnesses))) ∧
    IsPrivateFourCapAssignment color support terminal marked capFor ∧
    tree.splitAtPath path = some node ∧
    DecompositionTree.IsLowestSeparatingPath terminal tree path ∧
    DecompositionTree.FirstExitAlongPath terminal (1 : Fin 8)
      tree path false ∧
    DecompositionTree.FirstSetEscapeAlongPath privateCap tree path true ∧
    ¬∃ bucket, bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧
      ∃ y ∈ privateCap, ∃ z ∈ privateCap,
        y ≠ z ∧ y ∈ bucket ∧ z ∈ bucket := by
  exact ⟨support_decomposable, no_cap_five, no_cup_seven, no_strong_eight,
    terminal_mem_witnesses, terminal_is_terminal, private_assignment, path_lookup,
    terminal_lowest_path, owner_false_exit, privateCap_true_first_escape,
    no_privateCap_lowerSiblingBucket_collision⟩

end StructuralChargingNextState578PrivateCapTraceCounterexample
end ErdosSzekeres

end
