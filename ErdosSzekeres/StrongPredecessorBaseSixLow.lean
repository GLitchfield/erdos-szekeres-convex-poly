module

public import ErdosSzekeres.HalfPureSingletonFanFin10
public import ErdosSzekeres.StrongPredecessorBicoloring
public import ErdosSzekeres.SynchronizedFiveFanFin11WindowTransport
public import ErdosSzekeres.TripleColoringRealizability

@[expose] public section

/-!
# The low-cardinality predecessor-half theorem at six

The elementary predecessor bicoloring covers at most nine vertices. The exact
Fin10 singleton fan handles ten vertices, and the arbitrary-window Fin11
transport supplies a six-point strong-five-free support for eleven or twelve
vertices.
-/

namespace ErdosSzekeres

/-- Through twelve vertices, the completed elementary, Fin10, and Fin11
predecessor theorems supply a half-sized strong-five-free support. -/
theorem exists_predecessorHalfSubsetAtSix_of_card_le_twelve
    {n : ℕ} {χ : TripleColoring n}
    (hrealizable : IsSweepRealizable χ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6)
    (hn : n ≤ 12) :
    ∃ support : Finset (Fin n),
      ¬ContainsStrongPolygonSet χ support 5 ∧
      n ≤ 2 * support.card := by
  obtain ⟨P, rfl⟩ := hrealizable
  by_cases hnNine : n ≤ 9
  · obtain ⟨red, blue, hdisjoint, hunion, hred, hblue⟩ :=
      exists_strongPredecessorBicoloring_of_card_le_two_mul_sub_three
        (k := 6) (by omega) hnNine hnoStrong
    have hcard : n = red.card + blue.card := by
      have hunionCard := congrArg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisjoint] at hunionCard
      simpa using hunionCard.symm
    by_cases hle : blue.card ≤ red.card
    · exact ⟨red, by simpa using hred, by omega⟩
    · exact ⟨blue, by simpa using hblue, by omega⟩
  · by_cases hnTen : n = 10
    · subst n
      obtain ⟨side, _pivot, _hpivot, hhalf, hbranch⟩ :=
        halfPureSingletonFanAtSixFinTen_of_oneChange
          P.tripleColoring P.oneChangeOn_univ hnoStrong
      rcases hbranch with hlower | hupper
      · exact ⟨side,
          hlower.1.predecessorFree_lower_of_cupPure
            (by omega) (by simp) hnoStrong hlower.2,
          hhalf⟩
      · exact ⟨side,
          hupper.1.predecessorFree_upper_of_capPure
            (by omega) (by simp) hnoStrong hupper.2,
          hhalf⟩
    · have hnEleven : 11 ≤ n := by omega
      let f : Fin 11 ↪o Fin n := Fin.castLEOrderEmb hnEleven
      have honeWindow :
          OneChangeOn P.tripleColoring (Finset.univ.image f) := by
        intro i j k l hij hjk hkl _hi _hj _hk _hl
        exact P.oneChangeOn_univ hij hjk hkl (by simp) (by simp) (by simp) (by simp)
      have hnoStrongWindow :
          ¬ContainsStrongPolygonSet P.tripleColoring (Finset.univ.image f) 6 := by
        intro hstrong
        exact hnoStrong
          (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong (Finset.subset_univ _))
      obtain ⟨side, _hside, hsideCard, hsideFree⟩ :=
        predecessorFreeSixSubsetAtSixFinElevenWindow_of_oneChange
          P.tripleColoring f honeWindow hnoStrongWindow
      exact ⟨side, hsideFree, by omega⟩

end ErdosSzekeres

end
