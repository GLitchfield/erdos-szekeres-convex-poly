module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticInterface
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBranchV0150V1111
import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBranchV0151V1111
import ErdosSzekeres.SynchronizedFiveFanFin11Duality
import ErdosSzekeres.SynchronizedFiveFanFin11FourCaseSmoke

@[expose] public section

namespace ErdosSzekeres

/-!
# The unconditional Fin11 synchronized-five-fan endpoint

The two direct alternate-depth-two branch producers and their color duals
cover the four values of the frozen two-bit branch.
-/

/-- Every one-change Fin11 coloring without a strong hexagon has a synchronized five-fan side. -/
theorem synchronizedFiveFanSideAtSixFinEleven
    (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ ContainsStrongPolygonSet chi Finset.univ 6) :
    SynchronizedFiveFanFin11Conclusion chi := by
  exact synchronizedFiveFanSideAtSixFinEleven_of_fourBranches
    synchronizedFiveFanFin11PrimaryBranchForces_left_left
    (synchronizedFiveFanFin11BranchForces_dual
      (first := Turn.left) (second := Turn.right)
      synchronizedFiveFanFin11PrimaryBranchForces_right_left)
    synchronizedFiveFanFin11PrimaryBranchForces_right_left
    (synchronizedFiveFanFin11BranchForces_dual
      (first := Turn.right) (second := Turn.right)
      synchronizedFiveFanFin11PrimaryBranchForces_left_left)
    chi hone hnoStrong

end ErdosSzekeres

end
