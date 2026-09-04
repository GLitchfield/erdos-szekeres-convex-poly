module

public import ErdosSzekeres.Fin15AnchoredClauseChunk043
public import ErdosSzekeres.Fin15AnchoredClauseChunk044
public import ErdosSzekeres.Fin15AnchoredClauseChunk045

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 022. -/

theorem fin15Anchored_rejectSemanticSegment022
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi))) ∨
      (((¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi)))) ∨
      ((((Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi))) ∨
      (((¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi))))) ∨
      (((((Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi))) ∨
      (((¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi)))) ∨
      ((((Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi))) ∨
      (((¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi)) ∨
      ((¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi)))))) ∨
      ((((((Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi)) ∨
      ((Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi))) ∨
      (((¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi)) ∨
      ((¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi)))) ∨
      ((((Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi)) ∨
      ((¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi))) ∨
      (((¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      (¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi)) ∨
      ((Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi))))) ∨
      (((((Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi)) ∨
      ((¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi))) ∨
      (((¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi)) ∨
      ((Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi)))) ∨
      ((((Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi)) ∨
      ((¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi))) ∨
      (((¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi)) ∨
      ((Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi))))))) ∨
      ((((((Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      ((Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi))) ∨
      (((¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi)) ∨
      ((¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi)))) ∨
      ((((Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi)) ∨
      ((Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi))) ∨
      (((¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi)) ∨
      ((¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi))))) ∨
      (((((Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi)) ∨
      ((Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi))) ∨
      (((¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi)) ∨
      ((¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi)))) ∨
      ((((Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi)) ∨
      ((Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi))) ∨
      (((¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi)) ∨
      ((¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi)))))) ∨
      ((((((Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi)) ∨
      ((Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi))) ∨
      (((¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi)) ∨
      ((¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi)))) ∨
      ((((Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi)) ∨
      ((Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi))) ∨
      (((¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi)) ∨
      ((¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi))))) ∨
      (((((Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi)) ∨
      ((Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi))) ∨
      (((¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi)) ∨
      ((¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi)))) ∨
      ((((Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi)) ∨
      ((Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0453 chi))) ∨
      (((¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi)) ∨
      ((¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      ((Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0453 chi))) ∨
      (((Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi)))) ∨
      ((((¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0455 chi))) ∨
      (((Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi))))) ∨
      (((((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom0372 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom0372 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi)))) ∨
      ((((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom0373 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom0373 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom0374 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom0374 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0375 chi)))) ∨
      ((((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0375 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom0375 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom0375 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi))))) ∨
      (((((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom0376 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom0376 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi)))) ∨
      ((((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom0377 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom0377 chi)) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi) ∨
      ((¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi))) ∨
      (((Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom0378 chi) ∨
      (Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi)) ∨
      ((Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom0378 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi)))) ∨
      ((((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi))) ∨
      (((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom0379 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom0379 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi))))) ∨
      (((((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi))) ∨
      (((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi)))) ∨
      ((((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi))) ∨
      (((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi))) ∨
      (((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi)))) ∨
      ((((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi) ∨
      (¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi)) ∨
      ((¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi))) ∨
      (((Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi) ∨
      (Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi)) ∨
      ((Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi))))) ∨
      (((((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi))) ∨
      (((Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi)) ∨
      ((Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi)))) ∨
      ((((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi))) ∨
      (((Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi) ∨
      (Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi)) ∨
      ((¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi) ∨
      (¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi)))))))))) := by
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
                exact fin15Anchored_clause05552 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05553 chi hone hbad
                ·
                  exact fin15Anchored_clause05554 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05555 chi hone hbad
                ·
                  exact fin15Anchored_clause05556 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05557 chi hone hbad
                ·
                  exact fin15Anchored_clause05558 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05559 chi hone hbad
                ·
                  exact fin15Anchored_clause05560 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05561 chi hone hbad
                ·
                  exact fin15Anchored_clause05562 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05563 chi hone hbad
                ·
                  exact fin15Anchored_clause05564 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05565 chi hone hbad
                ·
                  exact fin15Anchored_clause05566 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05567 chi hone hbad
                ·
                  exact fin15Anchored_clause05568 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05569 chi hone hbad
                ·
                  exact fin15Anchored_clause05570 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05571 chi hone hbad
                ·
                  exact fin15Anchored_clause05572 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05573 chi hone hbad
                ·
                  exact fin15Anchored_clause05574 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05575 chi hone hbad
                ·
                  exact fin15Anchored_clause05576 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05577 chi hone hbad
                ·
                  exact fin15Anchored_clause05578 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05579 chi hone hbad
                ·
                  exact fin15Anchored_clause05580 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05581 chi hone hbad
                ·
                  exact fin15Anchored_clause05582 chi hone hbad
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
                  exact fin15Anchored_clause05583 chi hone hbad
                ·
                  exact fin15Anchored_clause05584 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05585 chi hone hbad
                ·
                  exact fin15Anchored_clause05586 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05587 chi hone hbad
                ·
                  exact fin15Anchored_clause05588 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05589 chi hone hbad
                ·
                  exact fin15Anchored_clause05590 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05591 chi hone hbad
                ·
                  exact fin15Anchored_clause05592 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05593 chi hone hbad
                ·
                  exact fin15Anchored_clause05594 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05595 chi hone hbad
                ·
                  exact fin15Anchored_clause05596 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05597 chi hone hbad
                ·
                  exact fin15Anchored_clause05598 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05599 chi hone hbad
                ·
                  exact fin15Anchored_clause05600 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05601 chi hone hbad
                ·
                  exact fin15Anchored_clause05602 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05603 chi hone hbad
                ·
                  exact fin15Anchored_clause05604 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05605 chi hone hbad
                ·
                  exact fin15Anchored_clause05606 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05607 chi hone hbad
                ·
                  exact fin15Anchored_clause05608 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05609 chi hone hbad
                ·
                  exact fin15Anchored_clause05610 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05611 chi hone hbad
                ·
                  exact fin15Anchored_clause05612 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05613 chi hone hbad
                ·
                  exact fin15Anchored_clause05614 chi hone hbad
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
                exact fin15Anchored_clause05615 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05616 chi hone hbad
                ·
                  exact fin15Anchored_clause05617 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05618 chi hone hbad
                ·
                  exact fin15Anchored_clause05619 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05620 chi hone hbad
                ·
                  exact fin15Anchored_clause05621 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05622 chi hone hbad
                ·
                  exact fin15Anchored_clause05623 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05624 chi hone hbad
                ·
                  exact fin15Anchored_clause05625 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05626 chi hone hbad
                ·
                  exact fin15Anchored_clause05627 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05628 chi hone hbad
                ·
                  exact fin15Anchored_clause05629 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05630 chi hone hbad
                ·
                  exact fin15Anchored_clause05631 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05632 chi hone hbad
                ·
                  exact fin15Anchored_clause05633 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05634 chi hone hbad
                ·
                  exact fin15Anchored_clause05635 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05636 chi hone hbad
                ·
                  exact fin15Anchored_clause05637 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05638 chi hone hbad
                ·
                  exact fin15Anchored_clause05639 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05640 chi hone hbad
                ·
                  exact fin15Anchored_clause05641 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05642 chi hone hbad
                ·
                  exact fin15Anchored_clause05643 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05644 chi hone hbad
                ·
                  exact fin15Anchored_clause05645 chi hone hbad
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
                  exact fin15Anchored_clause05646 chi hone hbad
                ·
                  exact fin15Anchored_clause05647 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05648 chi hone hbad
                ·
                  exact fin15Anchored_clause05649 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05650 chi hone hbad
                ·
                  exact fin15Anchored_clause05651 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05652 chi hone hbad
                ·
                  exact fin15Anchored_clause05653 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05654 chi hone hbad
                ·
                  exact fin15Anchored_clause05655 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05656 chi hone hbad
                ·
                  exact fin15Anchored_clause05657 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05658 chi hone hbad
                ·
                  exact fin15Anchored_clause05659 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05660 chi hone hbad
                ·
                  exact fin15Anchored_clause05661 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05662 chi hone hbad
                ·
                  exact fin15Anchored_clause05663 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05664 chi hone hbad
                ·
                  exact fin15Anchored_clause05665 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05666 chi hone hbad
                ·
                  exact fin15Anchored_clause05667 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05668 chi hone hbad
                ·
                  exact fin15Anchored_clause05669 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05670 chi hone hbad
                ·
                  exact fin15Anchored_clause05671 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05672 chi hone hbad
                ·
                  exact fin15Anchored_clause05673 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05674 chi hone hbad
                ·
                  exact fin15Anchored_clause05675 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05676 chi hone hbad
                ·
                  exact fin15Anchored_clause05677 chi hone hbad
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
                exact fin15Anchored_clause05678 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05679 chi hone hbad
                ·
                  exact fin15Anchored_clause05680 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05681 chi hone hbad
                ·
                  exact fin15Anchored_clause05682 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05683 chi hone hbad
                ·
                  exact fin15Anchored_clause05684 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05685 chi hone hbad
                ·
                  exact fin15Anchored_clause05686 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05687 chi hone hbad
                ·
                  exact fin15Anchored_clause05688 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05689 chi hone hbad
                ·
                  exact fin15Anchored_clause05690 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05691 chi hone hbad
                ·
                  exact fin15Anchored_clause05692 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05693 chi hone hbad
                ·
                  exact fin15Anchored_clause05694 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05695 chi hone hbad
                ·
                  exact fin15Anchored_clause05696 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05697 chi hone hbad
                ·
                  exact fin15Anchored_clause05698 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05699 chi hone hbad
                ·
                  exact fin15Anchored_clause05700 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05701 chi hone hbad
                ·
                  exact fin15Anchored_clause05702 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05703 chi hone hbad
                ·
                  exact fin15Anchored_clause05704 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05705 chi hone hbad
                ·
                  exact fin15Anchored_clause05706 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05707 chi hone hbad
                ·
                  exact fin15Anchored_clause05708 chi hone hbad
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
                  exact fin15Anchored_clause05709 chi hone hbad
                ·
                  exact fin15Anchored_clause05710 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05711 chi hone hbad
                ·
                  exact fin15Anchored_clause05712 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05713 chi hone hbad
                ·
                  exact fin15Anchored_clause05714 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05715 chi hone hbad
                ·
                  exact fin15Anchored_clause05716 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05717 chi hone hbad
                ·
                  exact fin15Anchored_clause05718 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05719 chi hone hbad
                ·
                  exact fin15Anchored_clause05720 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05721 chi hone hbad
                ·
                  exact fin15Anchored_clause05722 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05723 chi hone hbad
                ·
                  exact fin15Anchored_clause05724 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05725 chi hone hbad
                ·
                  exact fin15Anchored_clause05726 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05727 chi hone hbad
                ·
                  exact fin15Anchored_clause05728 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05729 chi hone hbad
                ·
                  exact fin15Anchored_clause05730 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05731 chi hone hbad
                ·
                  exact fin15Anchored_clause05732 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05733 chi hone hbad
                ·
                  exact fin15Anchored_clause05734 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05735 chi hone hbad
                ·
                  exact fin15Anchored_clause05736 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05737 chi hone hbad
                ·
                  exact fin15Anchored_clause05738 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05739 chi hone hbad
                ·
                  exact fin15Anchored_clause05740 chi hone hbad
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
                exact fin15Anchored_clause05741 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05742 chi hone hbad
                ·
                  exact fin15Anchored_clause05743 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05744 chi hone hbad
                ·
                  exact fin15Anchored_clause05745 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05746 chi hone hbad
                ·
                  exact fin15Anchored_clause05747 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05748 chi hone hbad
                ·
                  exact fin15Anchored_clause05749 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05750 chi hone hbad
                ·
                  exact fin15Anchored_clause05751 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05752 chi hone hbad
                ·
                  exact fin15Anchored_clause05753 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05754 chi hone hbad
                ·
                  exact fin15Anchored_clause05755 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05756 chi hone hbad
                ·
                  exact fin15Anchored_clause05757 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05758 chi hone hbad
                ·
                  exact fin15Anchored_clause05759 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05760 chi hone hbad
                ·
                  exact fin15Anchored_clause05761 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05762 chi hone hbad
                ·
                  exact fin15Anchored_clause05763 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05764 chi hone hbad
                ·
                  exact fin15Anchored_clause05765 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05766 chi hone hbad
                ·
                  exact fin15Anchored_clause05767 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05768 chi hone hbad
                ·
                  exact fin15Anchored_clause05769 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05770 chi hone hbad
                ·
                  exact fin15Anchored_clause05771 chi hone hbad
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
                  exact fin15Anchored_clause05772 chi hone hbad
                ·
                  exact fin15Anchored_clause05773 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05774 chi hone hbad
                ·
                  exact fin15Anchored_clause05775 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05776 chi hone hbad
                ·
                  exact fin15Anchored_clause05777 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05778 chi hone hbad
                ·
                  exact fin15Anchored_clause05779 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05780 chi hone hbad
                ·
                  exact fin15Anchored_clause05781 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05782 chi hone hbad
                ·
                  exact fin15Anchored_clause05783 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05784 chi hone hbad
                ·
                  exact fin15Anchored_clause05785 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05786 chi hone hbad
                ·
                  exact fin15Anchored_clause05787 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05788 chi hone hbad
                ·
                  exact fin15Anchored_clause05789 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05790 chi hone hbad
                ·
                  exact fin15Anchored_clause05791 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05792 chi hone hbad
                ·
                  exact fin15Anchored_clause05793 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05794 chi hone hbad
                ·
                  exact fin15Anchored_clause05795 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05796 chi hone hbad
                ·
                  exact fin15Anchored_clause05797 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05798 chi hone hbad
                ·
                  exact fin15Anchored_clause05799 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05800 chi hone hbad
                ·
                  exact fin15Anchored_clause05801 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause05802 chi hone hbad
                ·
                  exact fin15Anchored_clause05803 chi hone hbad

end ErdosSzekeres

end
