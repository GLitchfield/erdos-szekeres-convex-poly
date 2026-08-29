module

public import ErdosSzekeres.SynchronizedFiveFanFin11BranchInterface

@[expose] public section

namespace ErdosSzekeres

/-!
# Symbolic four-case aggregation at Fin 11

This certificate-free smoke theorem joins the four semantic branch producers
by eliminating the two frozen turn values.
-/

/-- Four two-bit branch producers cover every Fin11 coloring. -/
theorem synchronizedFiveFanSideAtSixFinEleven_of_fourBranches
    (hLeftLeft :
      SynchronizedFiveFanFin11BranchForces Turn.left Turn.left)
    (hLeftRight :
      SynchronizedFiveFanFin11BranchForces Turn.left Turn.right)
    (hRightLeft :
      SynchronizedFiveFanFin11BranchForces Turn.right Turn.left)
    (hRightRight :
      SynchronizedFiveFanFin11BranchForces Turn.right Turn.right)
    (chi : TripleColoring 11)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ ContainsStrongPolygonSet chi Finset.univ 6) :
    SynchronizedFiveFanFin11Conclusion chi := by
  cases hfirst : chi synchronizedFiveFanFin11BranchTriple0 with
  | left =>
      cases hsecond : chi synchronizedFiveFanFin11BranchTriple1 with
      | left =>
          exact hLeftLeft chi hone hnoStrong ⟨hfirst, hsecond⟩
      | right =>
          exact hLeftRight chi hone hnoStrong ⟨hfirst, hsecond⟩
  | right =>
      cases hsecond : chi synchronizedFiveFanFin11BranchTriple1 with
      | left =>
          exact hRightLeft chi hone hnoStrong ⟨hfirst, hsecond⟩
      | right =>
          exact hRightRight chi hone hnoStrong ⟨hfirst, hsecond⟩

end ErdosSzekeres

end
