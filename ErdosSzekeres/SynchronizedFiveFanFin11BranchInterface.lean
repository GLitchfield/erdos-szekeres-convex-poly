module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticInterface

@[expose] public section

namespace ErdosSzekeres

/-!
# The two-bit Fin11 branch interface

This certificate-free interface fixes the two leading selected-cube literals.
It is the common contract between direct certificate producers and color
duality.
-/

/-- The first frozen branch literal, manifest variable `v15`. -/
def synchronizedFiveFanFin11BranchTriple0 : OrderedTriple 11 :=
  ⟨0, 2, 8, by decide, by decide⟩

/-- The second frozen branch literal, manifest variable `v111`. -/
def synchronizedFiveFanFin11BranchTriple1 : OrderedTriple 11 :=
  ⟨3, 4, 6, by decide, by decide⟩

/-- The exact two-bit branch selected by the `v15` and `v111` literals. -/
def SynchronizedFiveFanFin11TwoBitBranch
    (first second : Turn) (chi : TripleColoring 11) : Prop :=
  chi synchronizedFiveFanFin11BranchTriple0 = first ∧
    chi synchronizedFiveFanFin11BranchTriple1 = second

/-- A semantic producer for one frozen two-bit branch. -/
def SynchronizedFiveFanFin11BranchForces
    (first second : Turn) : Prop :=
  ∀ (chi : TripleColoring 11),
    OneChangeOn chi Finset.univ →
    ¬ ContainsStrongPolygonSet chi Finset.univ 6 →
    SynchronizedFiveFanFin11TwoBitBranch first second chi →
    SynchronizedFiveFanFin11Conclusion chi

end ErdosSzekeres

end
