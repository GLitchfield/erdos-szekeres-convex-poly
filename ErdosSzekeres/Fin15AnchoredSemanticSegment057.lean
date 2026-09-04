module

public import ErdosSzekeres.Fin15AnchoredClauseChunk112
public import ErdosSzekeres.Fin15AnchoredClauseChunk113
public import ErdosSzekeres.Fin15AnchoredClauseChunk114

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 057. -/

theorem fin15Anchored_rejectSemanticSegment057
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1686 chi) ∨
      ((Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1686 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1687 chi))) ∨
      (((¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1687 chi) ∨
      (¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1687 chi)) ∨
      ((¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1687 chi) ∨
      (Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1687 chi)))) ∨
      ((((¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi)) ∨
      ((¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi))) ∨
      (((¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi) ∨
      (Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi)) ∨
      ((Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1688 chi))))) ∨
      (((((Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1688 chi) ∨
      (¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1689 chi)) ∨
      ((¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi) ∨
      (¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1689 chi))) ∨
      (((¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi) ∨
      (Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi)) ∨
      ((Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1689 chi) ∨
      (Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi)))) ∨
      ((((Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1689 chi) ∨
      (Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1689 chi)) ∨
      ((¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1690 chi) ∨
      (¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1690 chi))) ∨
      (((¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1690 chi) ∨
      (¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1690 chi)) ∨
      ((Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1690 chi) ∨
      (Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1690 chi)))))) ∨
      ((((((Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1690 chi) ∨
      (Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1690 chi)) ∨
      ((¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1691 chi) ∨
      (¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi))) ∨
      (((¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1691 chi) ∨
      (¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi)) ∨
      ((¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi) ∨
      (Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi)))) ∨
      ((((Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi) ∨
      (Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1691 chi)) ∨
      ((Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1691 chi) ∨
      (Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1691 chi))) ∨
      (((¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1692 chi) ∨
      (¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi)) ∨
      ((¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1692 chi) ∨
      (¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi))))) ∨
      (((((¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi) ∨
      (Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi)) ∨
      ((Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1692 chi) ∨
      (Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1692 chi))) ∨
      (((Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1692 chi) ∨
      (¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1693 chi)) ∨
      ((¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi) ∨
      (¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1693 chi)))) ∨
      ((((¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi) ∨
      (¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi)) ∨
      ((Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi) ∨
      (Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi))) ∨
      (((Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1693 chi) ∨
      (Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      Fin15AnchoredAtom1693 chi)) ∨
      ((¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1694 chi) ∨
      (¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) ∨
      ((¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1694 chi) ∨
      (¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi))) ∨
      (((¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) ∨
      (Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi)) ∨
      ((Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) ∨
      (Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1694 chi)))) ∨
      ((((Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1694 chi) ∨
      (Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1694 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1695 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi))) ∨
      (((¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1695 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi))))) ∨
      (((((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1695 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom1695 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom1695 chi))) ∨
      (((¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1696 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1696 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1696 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1696 chi)))) ∨
      ((((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1696 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1696 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1696 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1696 chi))) ∨
      (((¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi)))))) ∨
      ((((((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1698 chi))) ∨
      (((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1698 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1699 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1699 chi)))) ∨
      ((((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi))) ∨
      (((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1699 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1699 chi))))) ∨
      (((((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1699 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1700 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1700 chi))) ∨
      (((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) ∨
      (¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi)) ∨
      ((¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi)))) ∨
      ((((Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi)) ∨
      ((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1700 chi) ∨
      (Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1700 chi))) ∨
      (((Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1700 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1701 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1701 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1701 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1701 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1701 chi)))) ∨
      ((((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1702 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1702 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1702 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1702 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1702 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1702 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1703 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi))))) ∨
      (((((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1703 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1703 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi)))) ∨
      ((((Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1703 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1703 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi))) ∨
      (((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1704 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi)))))) ∨
      ((((((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1704 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1704 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1704 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi)))) ∨
      ((((¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi)) ∨
      ((¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi))) ∨
      (((Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1705 chi)) ∨
      ((Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi) ∨
      (Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1705 chi))))) ∨
      (((((Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1705 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1706 chi)) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1706 chi))) ∨
      (((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi)) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi)))) ∨
      ((((Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1706 chi)) ∨
      ((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1706 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1706 chi))) ∨
      (((¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1707 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi)) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1707 chi))))))) ∨
      (((((((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi)) ∨
      ((Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1707 chi))) ∨
      (((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1707 chi)) ∨
      ((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1707 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1708 chi)))) ∨
      ((((¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi)) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1708 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi))) ∨
      (((Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi)) ∨
      ((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1708 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1708 chi))))) ∨
      (((((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1708 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1709 chi)) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1709 chi))) ∨
      (((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) ∨
      (¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi)) ∨
      ((¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi)))) ∨
      ((((Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi)) ∨
      ((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1709 chi) ∨
      (Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1709 chi))) ∨
      (((Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1709 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1710 chi)) ∨
      ((¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1710 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1710 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1710 chi) ∨
      (Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1710 chi)) ∨
      ((Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1710 chi) ∨
      (Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1710 chi))) ∨
      (((Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1710 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1711 chi)) ∨
      ((¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1711 chi) ∨
      (Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1711 chi)))) ∨
      ((((¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1712 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1712 chi)) ∨
      ((¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1712 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1712 chi))) ∨
      (((¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1712 chi) ∨
      (¬Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1712 chi)) ∨
      ((¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1713 chi) ∨
      (¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi))))) ∨
      (((((¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1713 chi) ∨
      (¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi)) ∨
      ((Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi) ∨
      (Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi))) ∨
      (((Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1713 chi) ∨
      (Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1713 chi)) ∨
      ((Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1713 chi) ∨
      (¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1714 chi)))) ∨
      ((((¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1714 chi) ∨
      (¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1714 chi)) ∨
      ((¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1714 chi) ∨
      (Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1714 chi))) ∨
      (((Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1714 chi) ∨
      (Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1714 chi)) ∨
      ((Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1714 chi) ∨
      (¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1715 chi)))))))))) := by
  intro hbad
  rcases hbad with hbad | hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause14386 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14387 chi hbad
                ·
                  exact fin15Anchored_clause14388 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14389 chi hbad
                ·
                  exact fin15Anchored_clause14390 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14391 chi hbad
                ·
                  exact fin15Anchored_clause14392 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14393 chi hbad
                ·
                  exact fin15Anchored_clause14394 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14395 chi hbad
                ·
                  exact fin15Anchored_clause14396 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14397 chi hbad
                ·
                  exact fin15Anchored_clause14398 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14399 chi hbad
                ·
                  exact fin15Anchored_clause14400 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14401 chi hbad
                ·
                  exact fin15Anchored_clause14402 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14403 chi hbad
                ·
                  exact fin15Anchored_clause14404 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14405 chi hbad
                ·
                  exact fin15Anchored_clause14406 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14407 chi hbad
                ·
                  exact fin15Anchored_clause14408 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14409 chi hbad
                ·
                  exact fin15Anchored_clause14410 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14411 chi hbad
                ·
                  exact fin15Anchored_clause14412 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14413 chi hbad
                ·
                  exact fin15Anchored_clause14414 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14415 chi hbad
                ·
                  exact fin15Anchored_clause14416 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14417 chi hbad
                ·
                  exact fin15Anchored_clause14418 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14419 chi hbad
                ·
                  exact fin15Anchored_clause14420 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14421 chi hbad
                ·
                  exact fin15Anchored_clause14422 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14423 chi hbad
                ·
                  exact fin15Anchored_clause14424 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14425 chi hbad
                ·
                  exact fin15Anchored_clause14426 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14427 chi hbad
                ·
                  exact fin15Anchored_clause14428 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14429 chi hbad
                ·
                  exact fin15Anchored_clause14430 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14431 chi hbad
                ·
                  exact fin15Anchored_clause14432 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14433 chi hbad
                ·
                  exact fin15Anchored_clause14434 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14435 chi hbad
                ·
                  exact fin15Anchored_clause14436 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14437 chi hbad
                ·
                  exact fin15Anchored_clause14438 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14439 chi hbad
                ·
                  exact fin15Anchored_clause14440 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14441 chi hbad
                ·
                  exact fin15Anchored_clause14442 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14443 chi hbad
                ·
                  exact fin15Anchored_clause14444 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14445 chi hbad
                ·
                  exact fin15Anchored_clause14446 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14447 chi hbad
                ·
                  exact fin15Anchored_clause14448 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause14449 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14450 chi hbad
                ·
                  exact fin15Anchored_clause14451 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14452 chi hbad
                ·
                  exact fin15Anchored_clause14453 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14454 chi hbad
                ·
                  exact fin15Anchored_clause14455 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14456 chi hbad
                ·
                  exact fin15Anchored_clause14457 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14458 chi hbad
                ·
                  exact fin15Anchored_clause14459 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14460 chi hbad
                ·
                  exact fin15Anchored_clause14461 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14462 chi hbad
                ·
                  exact fin15Anchored_clause14463 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14464 chi hbad
                ·
                  exact fin15Anchored_clause14465 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14466 chi hbad
                ·
                  exact fin15Anchored_clause14467 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14468 chi hbad
                ·
                  exact fin15Anchored_clause14469 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14470 chi hbad
                ·
                  exact fin15Anchored_clause14471 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14472 chi hbad
                ·
                  exact fin15Anchored_clause14473 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14474 chi hbad
                ·
                  exact fin15Anchored_clause14475 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14476 chi hbad
                ·
                  exact fin15Anchored_clause14477 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14478 chi hbad
                ·
                  exact fin15Anchored_clause14479 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14480 chi hbad
                ·
                  exact fin15Anchored_clause14481 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14482 chi hbad
                ·
                  exact fin15Anchored_clause14483 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14484 chi hbad
                ·
                  exact fin15Anchored_clause14485 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14486 chi hbad
                ·
                  exact fin15Anchored_clause14487 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14488 chi hbad
                ·
                  exact fin15Anchored_clause14489 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14490 chi hbad
                ·
                  exact fin15Anchored_clause14491 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14492 chi hbad
                ·
                  exact fin15Anchored_clause14493 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14494 chi hbad
                ·
                  exact fin15Anchored_clause14495 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14496 chi hbad
                ·
                  exact fin15Anchored_clause14497 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14498 chi hbad
                ·
                  exact fin15Anchored_clause14499 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14500 chi hbad
                ·
                  exact fin15Anchored_clause14501 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14502 chi hbad
                ·
                  exact fin15Anchored_clause14503 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14504 chi hbad
                ·
                  exact fin15Anchored_clause14505 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14506 chi hbad
                ·
                  exact fin15Anchored_clause14507 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14508 chi hbad
                ·
                  exact fin15Anchored_clause14509 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14510 chi hbad
                ·
                  exact fin15Anchored_clause14511 chi hbad
  ·
    rcases hbad with hbad | hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact fin15Anchored_clause14512 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14513 chi hbad
                ·
                  exact fin15Anchored_clause14514 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14515 chi hbad
                ·
                  exact fin15Anchored_clause14516 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14517 chi hbad
                ·
                  exact fin15Anchored_clause14518 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14519 chi hbad
                ·
                  exact fin15Anchored_clause14520 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14521 chi hbad
                ·
                  exact fin15Anchored_clause14522 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14523 chi hbad
                ·
                  exact fin15Anchored_clause14524 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14525 chi hbad
                ·
                  exact fin15Anchored_clause14526 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14527 chi hbad
                ·
                  exact fin15Anchored_clause14528 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14529 chi hbad
                ·
                  exact fin15Anchored_clause14530 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14531 chi hbad
                ·
                  exact fin15Anchored_clause14532 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14533 chi hbad
                ·
                  exact fin15Anchored_clause14534 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14535 chi hbad
                ·
                  exact fin15Anchored_clause14536 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14537 chi hbad
                ·
                  exact fin15Anchored_clause14538 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14539 chi hbad
                ·
                  exact fin15Anchored_clause14540 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14541 chi hbad
                ·
                  exact fin15Anchored_clause14542 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14543 chi hbad
                ·
                  exact fin15Anchored_clause14544 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14545 chi hbad
                ·
                  exact fin15Anchored_clause14546 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14547 chi hbad
                ·
                  exact fin15Anchored_clause14548 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14549 chi hbad
                ·
                  exact fin15Anchored_clause14550 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14551 chi hbad
                ·
                  exact fin15Anchored_clause14552 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14553 chi hbad
                ·
                  exact fin15Anchored_clause14554 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14555 chi hbad
                ·
                  exact fin15Anchored_clause14556 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14557 chi hbad
                ·
                  exact fin15Anchored_clause14558 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14559 chi hbad
                ·
                  exact fin15Anchored_clause14560 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14561 chi hbad
                ·
                  exact fin15Anchored_clause14562 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14563 chi hbad
                ·
                  exact fin15Anchored_clause14564 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14565 chi hbad
                ·
                  exact fin15Anchored_clause14566 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14567 chi hbad
                ·
                  exact fin15Anchored_clause14568 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14569 chi hbad
                ·
                  exact fin15Anchored_clause14570 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14571 chi hbad
                ·
                  exact fin15Anchored_clause14572 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14573 chi hbad
                ·
                  exact fin15Anchored_clause14574 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14575 chi hbad
                ·
                  exact fin15Anchored_clause14576 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14577 chi hbad
                ·
                  exact fin15Anchored_clause14578 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14579 chi hbad
                ·
                  exact fin15Anchored_clause14580 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14581 chi hbad
                ·
                  exact fin15Anchored_clause14582 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14583 chi hbad
                ·
                  exact fin15Anchored_clause14584 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14585 chi hbad
                ·
                  exact fin15Anchored_clause14586 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14587 chi hbad
                ·
                  exact fin15Anchored_clause14588 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14589 chi hbad
                ·
                  exact fin15Anchored_clause14590 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14591 chi hbad
                ·
                  exact fin15Anchored_clause14592 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14593 chi hbad
                ·
                  exact fin15Anchored_clause14594 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14595 chi hbad
                ·
                  exact fin15Anchored_clause14596 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14597 chi hbad
                ·
                  exact fin15Anchored_clause14598 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14599 chi hbad
                ·
                  exact fin15Anchored_clause14600 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14601 chi hbad
                ·
                  exact fin15Anchored_clause14602 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14603 chi hbad
                ·
                  exact fin15Anchored_clause14604 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14605 chi hbad
                ·
                  exact fin15Anchored_clause14606 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14607 chi hbad
                ·
                  exact fin15Anchored_clause14608 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14609 chi hbad
                ·
                  exact fin15Anchored_clause14610 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14611 chi hbad
                ·
                  exact fin15Anchored_clause14612 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14613 chi hbad
                ·
                  exact fin15Anchored_clause14614 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14615 chi hbad
                ·
                  exact fin15Anchored_clause14616 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14617 chi hbad
                ·
                  exact fin15Anchored_clause14618 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14619 chi hbad
                ·
                  exact fin15Anchored_clause14620 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14621 chi hbad
                ·
                  exact fin15Anchored_clause14622 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14623 chi hbad
                ·
                  exact fin15Anchored_clause14624 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14625 chi hbad
                ·
                  exact fin15Anchored_clause14626 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14627 chi hbad
                ·
                  exact fin15Anchored_clause14628 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14629 chi hbad
                ·
                  exact fin15Anchored_clause14630 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14631 chi hbad
                ·
                  exact fin15Anchored_clause14632 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14633 chi hbad
                ·
                  exact fin15Anchored_clause14634 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14635 chi hbad
                ·
                  exact fin15Anchored_clause14636 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause14637 chi hbad
                ·
                  exact fin15Anchored_clause14638 chi hbad

end ErdosSzekeres

end
