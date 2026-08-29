module

public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2Endpoint

@[expose] public section

namespace ErdosSzekeres

/-- The unconditional Fin11 fan supplies a predecessor-free half support. -/
theorem predecessorHalfSubsetAtSixFinEleven_of_oneChange
    (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ ContainsStrongPolygonSet chi Finset.univ 6) :
    ∃ side : Finset (Fin 11),
      ¬ ContainsStrongPolygonSet chi side 5 ∧
        11 ≤ 2 * side.card := by
  obtain ⟨side, pivot, _hpivot, hcard, hbranch⟩ :=
    synchronizedFiveFanSideAtSixFinEleven chi hone hnoStrong
  rcases hbranch with hlower | hupper
  · refine ⟨side, ?_, by omega⟩
    exact hlower.1.predecessorFree_lower_of_cupPure
      (by omega) (by simp) hnoStrong hlower.2
  · refine ⟨side, ?_, by omega⟩
    exact hupper.1.predecessorFree_upper_of_capPure
      (by omega) (by simp) hnoStrong hupper.2

end ErdosSzekeres

end
