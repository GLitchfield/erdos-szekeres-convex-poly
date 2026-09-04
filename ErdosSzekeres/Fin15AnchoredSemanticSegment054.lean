module

public import ErdosSzekeres.Fin15AnchoredClauseChunk106
public import ErdosSzekeres.Fin15AnchoredClauseChunk107
public import ErdosSzekeres.Fin15AnchoredClauseChunk108

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 054. -/

theorem fin15Anchored_rejectSemanticSegment054
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1593 chi) ∨
      ((¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1593 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1593 chi))) ∨
      (((Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1593 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1593 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1593 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1593 chi)))) ∨
      ((((¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1594 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1594 chi)) ∨
      ((¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1594 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1594 chi))) ∨
      (((Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1594 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1594 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1594 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1594 chi))))) ∨
      (((((¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1595 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1595 chi)) ∨
      ((Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1595 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1595 chi))) ∨
      (((Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1595 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1595 chi)) ∨
      ((¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1596 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi)))) ∨
      ((((¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi)) ∨
      ((Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi))) ∨
      (((¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1597 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi)) ∨
      ((¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi)))))) ∨
      ((((((Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi)) ∨
      ((¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1598 chi) ∨
      (¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi))) ∨
      (((¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1598 chi) ∨
      (¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi)) ∨
      ((¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi) ∨
      (Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi)))) ∨
      ((((Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi) ∨
      (Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1598 chi)) ∨
      ((Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi) ∨
      (Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1598 chi))) ∨
      (((¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1599 chi) ∨
      (¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi)) ∨
      ((¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1599 chi) ∨
      (¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi))))) ∨
      (((((Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi) ∨
      (Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi)) ∨
      ((Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1599 chi) ∨
      (Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi))) ∨
      (((Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1599 chi) ∨
      (¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1600 chi)) ∨
      ((¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1600 chi) ∨
      (¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1600 chi)))) ∨
      ((((¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1600 chi) ∨
      (Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1600 chi)) ∨
      ((Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1600 chi) ∨
      (Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1600 chi))) ∨
      (((Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1600 chi) ∨
      (¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1601 chi)) ∨
      ((¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) ∨
      (¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1601 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) ∨
      ((¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) ∨
      (¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi))) ∨
      (((Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) ∨
      (Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1601 chi)) ∨
      ((Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) ∨
      (Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1601 chi)))) ∨
      ((((¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1602 chi) ∨
      (¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1602 chi)) ∨
      ((¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1602 chi) ∨
      (¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1602 chi))) ∨
      (((¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1602 chi) ∨
      (Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1602 chi)) ∨
      ((Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1602 chi) ∨
      (Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1602 chi))))) ∨
      (((((¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi)) ∨
      ((¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1604 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi))) ∨
      (((¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi)) ∨
      ((Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi) ∨
      (Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1604 chi)))) ∨
      ((((Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1604 chi) ∨
      (Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1604 chi)) ∨
      ((¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1605 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi))) ∨
      (((¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1605 chi)) ∨
      ((¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi)))))) ∨
      ((((((Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi) ∨
      (Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi)) ∨
      ((Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1605 chi) ∨
      (Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1605 chi))) ∨
      (((Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1605 chi) ∨
      (¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1606 chi)) ∨
      ((¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi) ∨
      (¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1606 chi)))) ∨
      ((((¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi) ∨
      (¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi)) ∨
      ((¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi) ∨
      (Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi))) ∨
      (((Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1606 chi) ∨
      (Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1606 chi)) ∨
      ((Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1606 chi) ∨
      (¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1607 chi))))) ∨
      (((((¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi) ∨
      (¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1607 chi)) ∨
      ((¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi) ∨
      (¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi))) ∨
      (((Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi) ∨
      (Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi)) ∨
      ((Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1607 chi) ∨
      (Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1607 chi)))) ∨
      ((((Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1607 chi) ∨
      (¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1608 chi)) ∨
      ((¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1608 chi) ∨
      (¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1608 chi))) ∨
      (((¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1608 chi) ∨
      (Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1608 chi)) ∨
      ((Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1608 chi) ∨
      (Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1608 chi)))))))) ∨
      (((((((¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1610 chi) ∨
      ((¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi) ∨
      (¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi))) ∨
      (((¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1610 chi) ∨
      (¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi)) ∨
      ((¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi) ∨
      (Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi)))) ∨
      ((((Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1610 chi) ∨
      (Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1610 chi)) ∨
      ((Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1610 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1611 chi))) ∨
      (((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1611 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi))))) ∨
      (((((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1611 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi ∧
      Fin15AnchoredAtom1611 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi ∧
      ¬Fin15AnchoredAtom1611 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1612 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi)))) ∨
      ((((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1612 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1612 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi ∧
      Fin15AnchoredAtom1612 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi ∧
      ¬Fin15AnchoredAtom1612 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1613 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1613 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi))) ∨
      (((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1613 chi)))) ∨
      ((((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi ∧
      Fin15AnchoredAtom1613 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi ∧
      ¬Fin15AnchoredAtom1613 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1614 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1614 chi))) ∨
      (((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      Fin15AnchoredAtom1614 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1614 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi ∧
      ¬Fin15AnchoredAtom1614 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1615 chi))))) ∨
      (((((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1615 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi))) ∨
      (((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1615 chi)))) ∨
      ((((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi ∧
      Fin15AnchoredAtom1615 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi ∧
      ¬Fin15AnchoredAtom1615 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1616 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi))) ∨
      (((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1616 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi))))))) ∨
      ((((((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1616 chi) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi ∧
      Fin15AnchoredAtom1616 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi ∧
      ¬Fin15AnchoredAtom1616 chi))) ∨
      (((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1617 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1617 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi)))) ∨
      ((((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1617 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi ∧
      Fin15AnchoredAtom1617 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi ∧
      ¬Fin15AnchoredAtom1617 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1618 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi))))) ∨
      (((((¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1618 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi))) ∨
      (((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1618 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi ∧
      Fin15AnchoredAtom1618 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi ∧
      ¬Fin15AnchoredAtom1618 chi)))) ∨
      ((((¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi))) ∨
      (((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi ∧
      Fin15AnchoredAtom1619 chi)))))) ∨
      ((((((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi ∧
      ¬Fin15AnchoredAtom1619 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1621 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi))) ∨
      (((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1621 chi)))) ∨
      ((((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi ∧
      Fin15AnchoredAtom1621 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi ∧
      ¬Fin15AnchoredAtom1621 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1622 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi))) ∨
      (((¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1622 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi))))) ∨
      (((((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1622 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi ∧
      Fin15AnchoredAtom1622 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi ∧
      ¬Fin15AnchoredAtom1622 chi))) ∨
      (((¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1623 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1623 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi)))) ∨
      ((((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1623 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi ∧
      Fin15AnchoredAtom1623 chi))) ∨
      (((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi ∧
      ¬Fin15AnchoredAtom1623 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1624 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      Fin15AnchoredAtom1624 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi ∧
      ¬Fin15AnchoredAtom1624 chi)))))))))) := by
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
                exact fin15Anchored_clause13629 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13630 chi hbad
                ·
                  exact fin15Anchored_clause13631 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13632 chi hbad
                ·
                  exact fin15Anchored_clause13633 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13634 chi hbad
                ·
                  exact fin15Anchored_clause13635 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13636 chi hbad
                ·
                  exact fin15Anchored_clause13637 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13638 chi hbad
                ·
                  exact fin15Anchored_clause13639 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13640 chi hbad
                ·
                  exact fin15Anchored_clause13641 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13642 chi hbad
                ·
                  exact fin15Anchored_clause13643 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13644 chi hbad
                ·
                  exact fin15Anchored_clause13645 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13646 chi hbad
                ·
                  exact fin15Anchored_clause13647 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13648 chi hbad
                ·
                  exact fin15Anchored_clause13649 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13650 chi hbad
                ·
                  exact fin15Anchored_clause13651 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13652 chi hbad
                ·
                  exact fin15Anchored_clause13653 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13654 chi hbad
                ·
                  exact fin15Anchored_clause13655 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13656 chi hbad
                ·
                  exact fin15Anchored_clause13657 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13658 chi hbad
                ·
                  exact fin15Anchored_clause13659 chi hbad
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
                  exact fin15Anchored_clause13660 chi hbad
                ·
                  exact fin15Anchored_clause13661 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13662 chi hbad
                ·
                  exact fin15Anchored_clause13663 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13664 chi hbad
                ·
                  exact fin15Anchored_clause13665 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13666 chi hbad
                ·
                  exact fin15Anchored_clause13667 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13668 chi hbad
                ·
                  exact fin15Anchored_clause13669 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13670 chi hbad
                ·
                  exact fin15Anchored_clause13671 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13672 chi hbad
                ·
                  exact fin15Anchored_clause13673 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13674 chi hbad
                ·
                  exact fin15Anchored_clause13675 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13676 chi hbad
                ·
                  exact fin15Anchored_clause13677 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13678 chi hbad
                ·
                  exact fin15Anchored_clause13679 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13680 chi hbad
                ·
                  exact fin15Anchored_clause13681 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13682 chi hbad
                ·
                  exact fin15Anchored_clause13683 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13684 chi hbad
                ·
                  exact fin15Anchored_clause13685 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13686 chi hbad
                ·
                  exact fin15Anchored_clause13687 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13688 chi hbad
                ·
                  exact fin15Anchored_clause13689 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13690 chi hbad
                ·
                  exact fin15Anchored_clause13691 chi hbad
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
                exact fin15Anchored_clause13692 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13693 chi hbad
                ·
                  exact fin15Anchored_clause13694 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13695 chi hbad
                ·
                  exact fin15Anchored_clause13696 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13697 chi hbad
                ·
                  exact fin15Anchored_clause13698 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13699 chi hbad
                ·
                  exact fin15Anchored_clause13700 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13701 chi hbad
                ·
                  exact fin15Anchored_clause13702 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13703 chi hbad
                ·
                  exact fin15Anchored_clause13704 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13705 chi hbad
                ·
                  exact fin15Anchored_clause13706 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13707 chi hbad
                ·
                  exact fin15Anchored_clause13708 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13709 chi hbad
                ·
                  exact fin15Anchored_clause13710 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13711 chi hbad
                ·
                  exact fin15Anchored_clause13712 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13713 chi hbad
                ·
                  exact fin15Anchored_clause13714 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13715 chi hbad
                ·
                  exact fin15Anchored_clause13716 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13717 chi hbad
                ·
                  exact fin15Anchored_clause13718 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13719 chi hbad
                ·
                  exact fin15Anchored_clause13720 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13721 chi hbad
                ·
                  exact fin15Anchored_clause13722 chi hbad
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
                  exact fin15Anchored_clause13723 chi hbad
                ·
                  exact fin15Anchored_clause13724 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13725 chi hbad
                ·
                  exact fin15Anchored_clause13726 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13727 chi hbad
                ·
                  exact fin15Anchored_clause13728 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13729 chi hbad
                ·
                  exact fin15Anchored_clause13730 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13731 chi hbad
                ·
                  exact fin15Anchored_clause13732 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13733 chi hbad
                ·
                  exact fin15Anchored_clause13734 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13735 chi hbad
                ·
                  exact fin15Anchored_clause13736 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13737 chi hbad
                ·
                  exact fin15Anchored_clause13738 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13739 chi hbad
                ·
                  exact fin15Anchored_clause13740 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13741 chi hbad
                ·
                  exact fin15Anchored_clause13742 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13743 chi hbad
                ·
                  exact fin15Anchored_clause13744 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13745 chi hbad
                ·
                  exact fin15Anchored_clause13746 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13747 chi hbad
                ·
                  exact fin15Anchored_clause13748 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13749 chi hbad
                ·
                  exact fin15Anchored_clause13750 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13751 chi hbad
                ·
                  exact fin15Anchored_clause13752 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13753 chi hbad
                ·
                  exact fin15Anchored_clause13754 chi hbad
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
                exact fin15Anchored_clause13755 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13756 chi hbad
                ·
                  exact fin15Anchored_clause13757 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13758 chi hbad
                ·
                  exact fin15Anchored_clause13759 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13760 chi hbad
                ·
                  exact fin15Anchored_clause13761 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13762 chi hbad
                ·
                  exact fin15Anchored_clause13763 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13764 chi hbad
                ·
                  exact fin15Anchored_clause13765 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13766 chi hbad
                ·
                  exact fin15Anchored_clause13767 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13768 chi hbad
                ·
                  exact fin15Anchored_clause13769 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13770 chi hbad
                ·
                  exact fin15Anchored_clause13771 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13772 chi hbad
                ·
                  exact fin15Anchored_clause13773 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13774 chi hbad
                ·
                  exact fin15Anchored_clause13775 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13776 chi hbad
                ·
                  exact fin15Anchored_clause13777 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13778 chi hbad
                ·
                  exact fin15Anchored_clause13779 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13780 chi hbad
                ·
                  exact fin15Anchored_clause13781 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13782 chi hbad
                ·
                  exact fin15Anchored_clause13783 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13784 chi hbad
                ·
                  exact fin15Anchored_clause13785 chi hbad
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
                  exact fin15Anchored_clause13786 chi hbad
                ·
                  exact fin15Anchored_clause13787 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13788 chi hbad
                ·
                  exact fin15Anchored_clause13789 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13790 chi hbad
                ·
                  exact fin15Anchored_clause13791 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13792 chi hbad
                ·
                  exact fin15Anchored_clause13793 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13794 chi hbad
                ·
                  exact fin15Anchored_clause13795 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13796 chi hbad
                ·
                  exact fin15Anchored_clause13797 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13798 chi hbad
                ·
                  exact fin15Anchored_clause13799 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13800 chi hbad
                ·
                  exact fin15Anchored_clause13801 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13802 chi hbad
                ·
                  exact fin15Anchored_clause13803 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13804 chi hbad
                ·
                  exact fin15Anchored_clause13805 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13806 chi hbad
                ·
                  exact fin15Anchored_clause13807 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13808 chi hbad
                ·
                  exact fin15Anchored_clause13809 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13810 chi hbad
                ·
                  exact fin15Anchored_clause13811 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13812 chi hbad
                ·
                  exact fin15Anchored_clause13813 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13814 chi hbad
                ·
                  exact fin15Anchored_clause13815 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13816 chi hbad
                ·
                  exact fin15Anchored_clause13817 chi hbad
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
                exact fin15Anchored_clause13818 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13819 chi hbad
                ·
                  exact fin15Anchored_clause13820 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13821 chi hbad
                ·
                  exact fin15Anchored_clause13822 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13823 chi hbad
                ·
                  exact fin15Anchored_clause13824 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13825 chi hbad
                ·
                  exact fin15Anchored_clause13826 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13827 chi hbad
                ·
                  exact fin15Anchored_clause13828 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13829 chi hbad
                ·
                  exact fin15Anchored_clause13830 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13831 chi hbad
                ·
                  exact fin15Anchored_clause13832 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13833 chi hbad
                ·
                  exact fin15Anchored_clause13834 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13835 chi hbad
                ·
                  exact fin15Anchored_clause13836 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13837 chi hbad
                ·
                  exact fin15Anchored_clause13838 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13839 chi hbad
                ·
                  exact fin15Anchored_clause13840 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13841 chi hbad
                ·
                  exact fin15Anchored_clause13842 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13843 chi hbad
                ·
                  exact fin15Anchored_clause13844 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13845 chi hbad
                ·
                  exact fin15Anchored_clause13846 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13847 chi hbad
                ·
                  exact fin15Anchored_clause13848 chi hbad
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
                  exact fin15Anchored_clause13849 chi hbad
                ·
                  exact fin15Anchored_clause13850 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13851 chi hbad
                ·
                  exact fin15Anchored_clause13852 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13853 chi hbad
                ·
                  exact fin15Anchored_clause13854 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13855 chi hbad
                ·
                  exact fin15Anchored_clause13856 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13857 chi hbad
                ·
                  exact fin15Anchored_clause13858 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13859 chi hbad
                ·
                  exact fin15Anchored_clause13860 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13861 chi hbad
                ·
                  exact fin15Anchored_clause13862 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13863 chi hbad
                ·
                  exact fin15Anchored_clause13864 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13865 chi hbad
                ·
                  exact fin15Anchored_clause13866 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13867 chi hbad
                ·
                  exact fin15Anchored_clause13868 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13869 chi hbad
                ·
                  exact fin15Anchored_clause13870 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13871 chi hbad
                ·
                  exact fin15Anchored_clause13872 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13873 chi hbad
                ·
                  exact fin15Anchored_clause13874 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13875 chi hbad
                ·
                  exact fin15Anchored_clause13876 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13877 chi hbad
                ·
                  exact fin15Anchored_clause13878 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause13879 chi hbad
                ·
                  exact fin15Anchored_clause13880 chi hbad

end ErdosSzekeres

end
