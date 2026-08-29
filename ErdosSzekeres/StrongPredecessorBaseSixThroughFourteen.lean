module

public import ErdosSzekeres.PredecessorHalfFin13
public import ErdosSzekeres.StrongPredecessorBaseSixLow

@[expose] public section

/-!
# The low-cardinality predecessor-half theorem at six through fourteen points

The exact Fin13 support theorem transports through the first thirteen points of
any larger sweep.  Its seven-point support is therefore half-sized for ambient
cardinality thirteen or fourteen.
-/

namespace ErdosSzekeres

/-- Through fourteen vertices, the elementary, Fin10, Fin11, and Fin13
predecessor theorems supply a half-sized strong-five-free support. -/
theorem exists_predecessorHalfSubsetAtSix_of_card_le_fourteen
    {n : ℕ} {χ : TripleColoring n}
    (hrealizable : IsSweepRealizable χ)
    (hnoStrong : ¬ContainsStrongPolygonSet χ Finset.univ 6)
    (hn : n ≤ 14) :
    ∃ support : Finset (Fin n),
      ¬ContainsStrongPolygonSet χ support 5 ∧
      n ≤ 2 * support.card := by
  by_cases hnTwelve : n ≤ 12
  · exact exists_predecessorHalfSubsetAtSix_of_card_le_twelve
      hrealizable hnoStrong hnTwelve
  · obtain ⟨P, rfl⟩ := hrealizable
    have hnThirteen : 13 ≤ n := by omega
    let f : Fin 13 ↪o Fin n := Fin.castLEOrderEmb hnThirteen
    have honeWindow :
        OneChangeOn P.tripleColoring (Finset.univ.image f) := by
      intro i j k l hij hjk hkl _hi _hj _hk _hl
      exact P.oneChangeOn_univ hij hjk hkl
        (by simp) (by simp) (by simp) (by simp)
    have hnoStrongWindow :
        ¬ContainsStrongPolygonSet P.tripleColoring
          (Finset.univ.image f) 6 := by
      intro hstrong
      exact hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
          (Finset.subset_univ _))
    obtain ⟨support, _hsupport, hcard, hfree⟩ :=
      predecessorFreeSevenSubsetAtSixFinThirteenWindow_of_oneChange
        P.tripleColoring f honeWindow hnoStrongWindow
    exact ⟨support, hfree, by omega⟩

end ErdosSzekeres

end
