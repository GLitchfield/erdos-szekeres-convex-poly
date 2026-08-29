module

public import ErdosSzekeres.PredecessorHalfFin15CrossExterior
public import ErdosSzekeres.PredecessorHalfFin15CrossExteriorTripleOwner
public import ErdosSzekeres.PredecessorHalfFin15CrossExteriorPairOwner

@[expose] public section

/-!
# Common-owner cross-exterior extension in the Fin15 Fano branch

This module records the exact Ticket 0089 Lane-2 contract and its two premise
screens.  The attempted theorem reached the packet's hard resource stop while
kernel-checking the maximum-support premise of a possible countermodel, so no
positive theorem or counterexample theorem is declared here.
-/

namespace ErdosSzekeres

namespace Fin15CommonOwnerCrossPremiseScreen

/-- The triple-owner counterexample still has a common erased owner, but it
fails the frozen pairwise-distinct-block premises. -/
example : ¬(Fin15TripleCrossCounterexample.block5 ≠
      Fin15TripleCrossCounterexample.block5 ∧
    Fin15TripleCrossCounterexample.block5 ≠
      Fin15TripleCrossCounterexample.block1 ∧
    Fin15TripleCrossCounterexample.block5 ≠
      Fin15TripleCrossCounterexample.block1) := by
  simp

/-- The pair-owner counterexample has three distinct selected blocks, but
their three-way intersection is empty. -/
example : ¬∃ owner : Fin 15,
    owner ∈ Fin15PairOwnerCounterexample.first ∧
    owner ∈ Fin15PairOwnerCounterexample.second ∧
    owner ∈ Fin15PairOwnerCounterexample.third := by
  decide

end Fin15CommonOwnerCrossPremiseScreen

/-- The exact proposition of the frozen four-shape theorem.  This is a
statement record, not a proof of the proposition. -/
def Fin15CommonOwnerDistinctCrossExteriorContract : Prop :=
  ∀ (chi : TripleColoring 15) (_hone : OneChangeOn chi Finset.univ)
    {support first second third : Finset (Fin 15)}
    (blocks : Finset (Finset (Fin 15))) {q r s x y : Fin 15},
    IsMaximumPredecessorFreeSupport chi 6 support →
    support.card = 7 →
    blocks.card = 7 →
    (∀ block ∈ blocks, block ⊆ support) →
    (∀ block ∈ blocks, block.card = 4) →
    (∀ pair : Finset (Fin 15), pair ⊆ support → pair.card = 2 →
      ∃! block : Finset (Fin 15), block ∈ blocks ∧ pair ⊆ support \ block) →
    first ∈ blocks → second ∈ blocks → third ∈ blocks →
    first ≠ second → first ≠ third → second ≠ third →
    q ∈ Finset.univ \ support → r ∈ Finset.univ \ support →
    s ∈ Finset.univ \ support → q ≠ r → q ≠ s → r ≠ s →
    IsStrongPolygonSet chi (insert q first) →
    IsStrongPolygonSet chi (insert r second) →
    IsStrongPolygonSet chi (insert s third) →
    x ∈ first → x ∈ second → x ∈ third → y ∈ third → x ≠ y →
    Fin15ThreeExteriorMultiOwnerWitness chi support q r s x y →
    ∃ polygon : Finset (Fin 15), ∃ z : Fin 15,
      polygon ⊆ insert q (insert r (insert s support)) ∧
      polygon.card = 5 ∧ IsStrongPolygonSet chi polygon ∧
      z ∈ (first ∪ second ∪ third) \ polygon ∧
      IsStrongPolygonSet chi (insert z polygon)

/-- A common erased owner supplies all three killed-block facts required by
the four-way witness split; none is assumed independently. -/
theorem commonOwner_kills_selectedBlocks
    {support first second third : Finset (Fin 15)} {x y : Fin 15}
    (hxFirst : x ∈ first) (hxSecond : x ∈ second)
    (hxThird : x ∈ third) :
    ¬first ⊆ (support.erase x).erase y ∧
      ¬second ⊆ (support.erase x).erase y ∧
      ¬third ⊆ (support.erase x).erase y := by
  have hxNotDouble : x ∉ (support.erase x).erase y := by simp
  constructor
  · intro hsub
    exact hxNotDouble (hsub hxFirst)
  constructor
  · intro hsub
    exact hxNotDouble (hsub hxSecond)
  · intro hsub
    exact hxNotDouble (hsub hxThird)

/-
The frozen theorem

  fin15_fano_commonOwner_distinctBlocks_multiOwner_crossExterior_extension

was elaborated with the contract above and split into the exact four shapes.
The direct proof stopped at the first missing cross-color equality documented
in the owned proof notes.  A later exact countermodel candidate passed the
semantic premise probe, but its all-eight maximum-support kernel check exceeded
the immutable 10-GiB envelope and timed out.  Therefore neither the theorem nor
its negation is asserted at this bounded-stop terminal.
-/

end ErdosSzekeres

end
