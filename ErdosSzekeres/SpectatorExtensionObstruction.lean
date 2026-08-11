module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Uniform spectator extension obstruction

Two same-turn spectators over a monochromatic four-set already create a
monochromatic, hence strong, six-set.  This is the local obstruction met by
uniform-spectator attempts to lift Layer-F mutation controls to the exact
threshold.
-/

namespace ErdosSzekeres

/-- Every triple in `base ∪ extension` which uses at least one extension
vertex has one fixed turn. -/
def HasUniformMixedTurn {n : ℕ} (χ : TripleColoring n)
    (base extension : Finset (Fin n)) (turn : Turn) : Prop :=
  ∀ t : OrderedTriple n,
    t.i ∈ base ∪ extension → t.j ∈ base ∪ extension →
      t.k ∈ base ∪ extension →
      (t.i ∈ extension ∨ t.j ∈ extension ∨ t.k ∈ extension) →
        χ t = turn

/-- A cup remains a cup after adjoining vertices whose mixed triples all turn
left. -/
theorem IsCupSet.union_of_uniformMixedLeft
    {n : ℕ} {χ : TripleColoring n}
    {base extension : Finset (Fin n)}
    (hbase : IsCupSet χ base)
    (hmixed : HasUniformMixedTurn χ base extension Turn.left) :
    IsCupSet χ (base ∪ extension) := by
  intro t hi hj hk
  by_cases hiBase : t.i ∈ base
  · by_cases hjBase : t.j ∈ base
    · by_cases hkBase : t.k ∈ base
      · exact hbase t hiBase hjBase hkBase
      · exact hmixed t hi hj hk (Or.inr (Or.inr
          ((Finset.mem_union.mp hk).resolve_left hkBase)))
    · exact hmixed t hi hj hk (Or.inr (Or.inl
        ((Finset.mem_union.mp hj).resolve_left hjBase)))
  · exact hmixed t hi hj hk (Or.inl
      ((Finset.mem_union.mp hi).resolve_left hiBase))

/-- The color-dual uniform extension statement for caps. -/
theorem IsCapSet.union_of_uniformMixedRight
    {n : ℕ} {χ : TripleColoring n}
    {base extension : Finset (Fin n)}
    (hbase : IsCapSet χ base)
    (hmixed : HasUniformMixedTurn χ base extension Turn.right) :
    IsCapSet χ (base ∪ extension) := by
  intro t hi hj hk
  by_cases hiBase : t.i ∈ base
  · by_cases hjBase : t.j ∈ base
    · by_cases hkBase : t.k ∈ base
      · exact hbase t hiBase hjBase hkBase
      · exact hmixed t hi hj hk (Or.inr (Or.inr
          ((Finset.mem_union.mp hk).resolve_left hkBase)))
    · exact hmixed t hi hj hk (Or.inr (Or.inl
        ((Finset.mem_union.mp hj).resolve_left hjBase)))
  · exact hmixed t hi hj hk (Or.inl
      ((Finset.mem_union.mp hi).resolve_left hiBase))

/-- A cup-four plus two disjoint uniform-left spectators contains a strong
six-set—indeed, their union is a cup-six. -/
theorem containsStrongSix_of_cupFour_two_uniformLeft
    {n : ℕ} {χ : TripleColoring n}
    {base spectators ambient : Finset (Fin n)}
    (hbaseSub : base ⊆ ambient) (hspectatorsSub : spectators ⊆ ambient)
    (hdisjoint : Disjoint base spectators)
    (hbaseCard : base.card = 4) (hspectatorsCard : spectators.card = 2)
    (hcup : IsCupSet χ base)
    (hmixed : HasUniformMixedTurn χ base spectators Turn.left) :
    ContainsStrongPolygonSet χ ambient 6 := by
  have hunionSub : base ∪ spectators ⊆ ambient :=
    Finset.union_subset hbaseSub hspectatorsSub
  have hunionCard : (base ∪ spectators).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hbaseCard, hspectatorsCard]
  have hunionCup := hcup.union_of_uniformMixedLeft hmixed
  exact ⟨base ∪ spectators, hunionSub, hunionCard,
    FinsetPolygon.IsCupSet.isStrongPolygonSet hunionCup⟩

/-- A cap-four plus two disjoint uniform-right spectators contains a strong
six-set. -/
theorem containsStrongSix_of_capFour_two_uniformRight
    {n : ℕ} {χ : TripleColoring n}
    {base spectators ambient : Finset (Fin n)}
    (hbaseSub : base ⊆ ambient) (hspectatorsSub : spectators ⊆ ambient)
    (hdisjoint : Disjoint base spectators)
    (hbaseCard : base.card = 4) (hspectatorsCard : spectators.card = 2)
    (hcap : IsCapSet χ base)
    (hmixed : HasUniformMixedTurn χ base spectators Turn.right) :
    ContainsStrongPolygonSet χ ambient 6 := by
  have hunionSub : base ∪ spectators ⊆ ambient :=
    Finset.union_subset hbaseSub hspectatorsSub
  have hunionCard : (base ∪ spectators).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisjoint, hbaseCard, hspectatorsCard]
  have hunionCap := hcap.union_of_uniformMixedRight hmixed
  exact ⟨base ∪ spectators, hunionSub, hunionCard,
    FinsetPolygon.IsCapSet.isStrongPolygonSet hunionCap⟩

end ErdosSzekeres
