module

public import ErdosSzekeres.ES6Anchored
public import ErdosSzekeres.ES6Bridge

@[expose] public section

/-!
# Kernel-checked finite certificate for the seventeen-point case

`ES6Anchored.lean` replays the LRAT refutation of the anchored seventeen-point
signotope instance (680 triple variables; one-change clauses on every four
vertices, no strong six-set, and vertex `0` anchored) through 192 kernel-checked
checkpoint segments.  `ES6Bridge.lean` turns that conclusion into the planar
statements below.
-/

namespace ErdosSzekeres

theorem anchoredSeventeenForcesStrongSix : AnchoredSeventeenForcesStrongSix :=
  ES6.es6Anchored_of_oneChange

/-- Every swept configuration with at least seventeen vertices contains a
strong six-set. -/
theorem SweptConfiguration.exists_strong_six_of_seventeen_le
    {n : ℕ} (P : SweptConfiguration n) (hn : 17 ≤ n) :
    ContainsStrongPolygonSet P.tripleColoring Finset.univ 6 :=
  P.containsStrongSix_of_seventeen_le anchoredSeventeenForcesStrongSix hn

/-- The kernel-checked seventeen-point upper bound for the happy-ending problem
at six vertices. -/
theorem forces_six : ForcesConvexPolygon 6 17 :=
  forces_six_of_anchoredSeventeen anchoredSeventeenForcesStrongSix

/-- The happy-ending formula is exact at `n = 6`: seventeen points force a
convex hexagon, while sixteen points need not contain one. -/
theorem erdosSzekeresFormulaAt_six : ErdosSzekeresFormulaAt 6 :=
  erdosSzekeresFormulaAt_six_of_anchoredSeventeen anchoredSeventeenForcesStrongSix

end ErdosSzekeres

end
