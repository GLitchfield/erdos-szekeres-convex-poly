module

public import ErdosSzekeres.Fin15AnchoredClauseChunk051
public import ErdosSzekeres.Fin15AnchoredClauseChunk052
public import ErdosSzekeres.Fin15AnchoredClauseChunk053

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 026. -/

theorem fin15Anchored_rejectSemanticSegment026
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi) ∨
      ((Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0441 chi))) ∨
      (((¬Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi) ∨
      (¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi)) ∨
      ((¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      (¬Fin15AnchoredAtom0386 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi)))) ∨
      ((((Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0386 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0442 chi)) ∨
      ((¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi))) ∨
      (((¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi)) ∨
      ((Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0443 chi))))) ∨
      (((((Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0443 chi)) ∨
      ((¬Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi))) ∨
      (((¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi)) ∨
      ((Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0444 chi)))) ∨
      ((((Fin15AnchoredAtom0387 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0387 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0444 chi)) ∨
      ((¬Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi))) ∨
      (((¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (¬Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi)) ∨
      ((Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0445 chi)))))) ∨
      ((((((Fin15AnchoredAtom0388 chi ∧
      ¬Fin15AnchoredAtom0389 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi) ∨
      (Fin15AnchoredAtom0388 chi ∧
      Fin15AnchoredAtom0389 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0445 chi)) ∨
      ((¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi))) ∨
      (((¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi)) ∨
      ((Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0446 chi)))) ∨
      ((((Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi) ∨
      (Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0446 chi)) ∨
      ((¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi))) ∨
      (((¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi)) ∨
      ((Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0447 chi))))) ∨
      (((((Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi) ∨
      (Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0447 chi)) ∨
      ((¬Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0448 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0448 chi))) ∨
      (((¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi) ∨
      (¬Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0448 chi)) ∨
      ((Fin15AnchoredAtom0390 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi) ∨
      (Fin15AnchoredAtom0390 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0448 chi)))) ∨
      ((((¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi)) ∨
      ((¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi))) ∨
      (((Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0449 chi)) ∨
      ((Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi) ∨
      (Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0449 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      ((¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi))) ∨
      (((¬Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi)) ∨
      ((Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0450 chi) ∨
      (Fin15AnchoredAtom0391 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi)))) ∨
      ((((Fin15AnchoredAtom0391 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0450 chi) ∨
      (¬Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi)) ∨
      ((¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi))) ∨
      (((¬Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi)) ∨
      ((Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0451 chi) ∨
      (Fin15AnchoredAtom0392 chi ∧
      ¬Fin15AnchoredAtom0393 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi))))) ∨
      (((((Fin15AnchoredAtom0392 chi ∧
      Fin15AnchoredAtom0393 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0451 chi) ∨
      (¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi)) ∨
      ((¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi))) ∨
      (((¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi)) ∨
      ((Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0452 chi) ∨
      (Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi)))) ∨
      ((((Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0452 chi) ∨
      (¬Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi)) ∨
      ((¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi))) ∨
      (((¬Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi)) ∨
      ((Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0394 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi)))))) ∨
      ((((((Fin15AnchoredAtom0394 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0453 chi) ∨
      (Fin15AnchoredAtom0395 chi ∧
      ¬Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0454 chi)) ∨
      ((Fin15AnchoredAtom0395 chi ∧
      Fin15AnchoredAtom0396 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0454 chi) ∨
      (¬Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi))) ∨
      (((¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((¬Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi)))) ∨
      ((((Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      ¬Fin15AnchoredAtom0455 chi) ∨
      (Fin15AnchoredAtom0397 chi ∧
      ¬Fin15AnchoredAtom0398 chi ∧
      Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi)) ∨
      ((Fin15AnchoredAtom0397 chi ∧
      Fin15AnchoredAtom0398 chi ∧
      ¬Fin15AnchoredAtom0399 chi ∧
      Fin15AnchoredAtom0455 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi))) ∨
      (((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi)) ∨
      ((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi))))) ∨
      (((((Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0421 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi)) ∨
      ((Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0421 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi))) ∨
      (((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi)))) ∨
      ((((Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0423 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi)) ∨
      ((Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0423 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi))) ∨
      (((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi)) ∨
      ((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0424 chi) ∨
      ((Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0424 chi))) ∨
      (((¬Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi)) ∨
      ((¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (¬Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi)))) ∨
      ((((Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0425 chi)) ∨
      ((Fin15AnchoredAtom0400 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi) ∨
      (Fin15AnchoredAtom0400 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0425 chi))) ∨
      (((¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi)) ∨
      ((¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi))))) ∨
      (((((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0427 chi)) ∨
      ((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0427 chi))) ∨
      (((¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi)) ∨
      ((¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi)))) ∨
      ((((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0428 chi)) ∨
      ((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0428 chi))) ∨
      (((¬Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi)) ∨
      ((¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi)))))) ∨
      ((((((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0429 chi)) ∨
      ((Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi) ∨
      (Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0429 chi))) ∨
      (((¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi)) ∨
      ((¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi)))) ∨
      ((((Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0433 chi)) ∨
      ((Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi) ∨
      (Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0433 chi))) ∨
      (((¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi)) ∨
      ((¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi))))) ∨
      (((((Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0434 chi)) ∨
      ((Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi) ∨
      (Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0434 chi))) ∨
      (((¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi)) ∨
      ((¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi)))) ∨
      ((((Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom0435 chi)) ∨
      ((Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi) ∨
      (Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom0435 chi))) ∨
      (((¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi)) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi))))))) ∨
      ((((((Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      ((Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom0436 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi))) ∨
      (((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom0436 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi)) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi)))) ∨
      ((((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi)) ∨
      ((Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom0437 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi))) ∨
      (((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom0437 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi)) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi))))) ∨
      (((((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi)) ∨
      ((Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom0438 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi))) ∨
      (((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom0438 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi)) ∨
      ((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi)))) ∨
      ((((¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi)) ∨
      ((Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom0439 chi) ∨
      (Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi))) ∨
      (((Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom0439 chi) ∨
      (¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi)) ∨
      ((¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi)) ∨
      ((Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom0440 chi) ∨
      (Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi))) ∨
      (((Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom0440 chi) ∨
      (¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0441 chi)) ∨
      ((¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi)))) ∨
      ((((¬Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi)) ∨
      ((Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom0441 chi) ∨
      (Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi))) ∨
      (((Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom0441 chi) ∨
      (¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0442 chi)) ∨
      ((Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom0442 chi))))) ∨
      (((((Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0442 chi) ∨
      (Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom0442 chi)) ∨
      ((¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi))) ∨
      (((¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi)) ∨
      ((Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom0443 chi)))) ∨
      ((((Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi) ∨
      (Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom0443 chi)) ∨
      ((¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi))) ∨
      (((¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi)) ∨
      ((Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom0444 chi) ∨
      (Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom0444 chi)))))))))) := by
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
                exact fin15Anchored_clause06562 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06563 chi hone hbad
                ·
                  exact fin15Anchored_clause06564 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06565 chi hone hbad
                ·
                  exact fin15Anchored_clause06566 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06567 chi hone hbad
                ·
                  exact fin15Anchored_clause06568 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06569 chi hone hbad
                ·
                  exact fin15Anchored_clause06570 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06571 chi hone hbad
                ·
                  exact fin15Anchored_clause06572 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06573 chi hone hbad
                ·
                  exact fin15Anchored_clause06574 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06575 chi hone hbad
                ·
                  exact fin15Anchored_clause06576 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06577 chi hone hbad
                ·
                  exact fin15Anchored_clause06578 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06579 chi hone hbad
                ·
                  exact fin15Anchored_clause06580 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06581 chi hone hbad
                ·
                  exact fin15Anchored_clause06582 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06583 chi hone hbad
                ·
                  exact fin15Anchored_clause06584 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06585 chi hone hbad
                ·
                  exact fin15Anchored_clause06586 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06587 chi hone hbad
                ·
                  exact fin15Anchored_clause06588 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06589 chi hone hbad
                ·
                  exact fin15Anchored_clause06590 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06591 chi hone hbad
                ·
                  exact fin15Anchored_clause06592 chi hone hbad
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
                  exact fin15Anchored_clause06593 chi hone hbad
                ·
                  exact fin15Anchored_clause06594 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06595 chi hone hbad
                ·
                  exact fin15Anchored_clause06596 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06597 chi hone hbad
                ·
                  exact fin15Anchored_clause06598 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06599 chi hone hbad
                ·
                  exact fin15Anchored_clause06600 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06601 chi hone hbad
                ·
                  exact fin15Anchored_clause06602 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06603 chi hone hbad
                ·
                  exact fin15Anchored_clause06604 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06605 chi hone hbad
                ·
                  exact fin15Anchored_clause06606 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06607 chi hone hbad
                ·
                  exact fin15Anchored_clause06608 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06609 chi hone hbad
                ·
                  exact fin15Anchored_clause06610 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06611 chi hone hbad
                ·
                  exact fin15Anchored_clause06612 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06613 chi hone hbad
                ·
                  exact fin15Anchored_clause06614 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06615 chi hone hbad
                ·
                  exact fin15Anchored_clause06616 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06617 chi hone hbad
                ·
                  exact fin15Anchored_clause06618 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06619 chi hone hbad
                ·
                  exact fin15Anchored_clause06620 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06621 chi hone hbad
                ·
                  exact fin15Anchored_clause06622 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06623 chi hone hbad
                ·
                  exact fin15Anchored_clause06624 chi hone hbad
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
                exact fin15Anchored_clause06625 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06626 chi hone hbad
                ·
                  exact fin15Anchored_clause06627 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06628 chi hone hbad
                ·
                  exact fin15Anchored_clause06629 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06630 chi hone hbad
                ·
                  exact fin15Anchored_clause06631 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06632 chi hone hbad
                ·
                  exact fin15Anchored_clause06633 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06634 chi hone hbad
                ·
                  exact fin15Anchored_clause06635 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06636 chi hone hbad
                ·
                  exact fin15Anchored_clause06637 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06638 chi hone hbad
                ·
                  exact fin15Anchored_clause06639 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06640 chi hone hbad
                ·
                  exact fin15Anchored_clause06641 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06642 chi hone hbad
                ·
                  exact fin15Anchored_clause06643 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06644 chi hone hbad
                ·
                  exact fin15Anchored_clause06645 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06646 chi hone hbad
                ·
                  exact fin15Anchored_clause06647 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06648 chi hone hbad
                ·
                  exact fin15Anchored_clause06649 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06650 chi hone hbad
                ·
                  exact fin15Anchored_clause06651 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06652 chi hone hbad
                ·
                  exact fin15Anchored_clause06653 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06654 chi hone hbad
                ·
                  exact fin15Anchored_clause06655 chi hone hbad
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
                  exact fin15Anchored_clause06656 chi hone hbad
                ·
                  exact fin15Anchored_clause06657 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06658 chi hone hbad
                ·
                  exact fin15Anchored_clause06659 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06660 chi hone hbad
                ·
                  exact fin15Anchored_clause06661 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06662 chi hone hbad
                ·
                  exact fin15Anchored_clause06663 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06664 chi hone hbad
                ·
                  exact fin15Anchored_clause06665 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06666 chi hone hbad
                ·
                  exact fin15Anchored_clause06667 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06668 chi hone hbad
                ·
                  exact fin15Anchored_clause06669 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06670 chi hone hbad
                ·
                  exact fin15Anchored_clause06671 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06672 chi hone hbad
                ·
                  exact fin15Anchored_clause06673 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06674 chi hone hbad
                ·
                  exact fin15Anchored_clause06675 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06676 chi hone hbad
                ·
                  exact fin15Anchored_clause06677 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06678 chi hone hbad
                ·
                  exact fin15Anchored_clause06679 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06680 chi hone hbad
                ·
                  exact fin15Anchored_clause06681 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06682 chi hone hbad
                ·
                  exact fin15Anchored_clause06683 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06684 chi hone hbad
                ·
                  exact fin15Anchored_clause06685 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06686 chi hone hbad
                ·
                  exact fin15Anchored_clause06687 chi hone hbad
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
                exact fin15Anchored_clause06688 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06689 chi hone hbad
                ·
                  exact fin15Anchored_clause06690 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06691 chi hone hbad
                ·
                  exact fin15Anchored_clause06692 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06693 chi hone hbad
                ·
                  exact fin15Anchored_clause06694 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06695 chi hone hbad
                ·
                  exact fin15Anchored_clause06696 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06697 chi hone hbad
                ·
                  exact fin15Anchored_clause06698 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06699 chi hone hbad
                ·
                  exact fin15Anchored_clause06700 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06701 chi hone hbad
                ·
                  exact fin15Anchored_clause06702 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06703 chi hone hbad
                ·
                  exact fin15Anchored_clause06704 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06705 chi hone hbad
                ·
                  exact fin15Anchored_clause06706 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06707 chi hone hbad
                ·
                  exact fin15Anchored_clause06708 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06709 chi hone hbad
                ·
                  exact fin15Anchored_clause06710 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06711 chi hone hbad
                ·
                  exact fin15Anchored_clause06712 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06713 chi hone hbad
                ·
                  exact fin15Anchored_clause06714 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06715 chi hone hbad
                ·
                  exact fin15Anchored_clause06716 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06717 chi hone hbad
                ·
                  exact fin15Anchored_clause06718 chi hone hbad
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
                  exact fin15Anchored_clause06719 chi hone hbad
                ·
                  exact fin15Anchored_clause06720 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06721 chi hone hbad
                ·
                  exact fin15Anchored_clause06722 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06723 chi hone hbad
                ·
                  exact fin15Anchored_clause06724 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06725 chi hone hbad
                ·
                  exact fin15Anchored_clause06726 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06727 chi hone hbad
                ·
                  exact fin15Anchored_clause06728 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06729 chi hone hbad
                ·
                  exact fin15Anchored_clause06730 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06731 chi hone hbad
                ·
                  exact fin15Anchored_clause06732 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06733 chi hone hbad
                ·
                  exact fin15Anchored_clause06734 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06735 chi hone hbad
                ·
                  exact fin15Anchored_clause06736 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06737 chi hone hbad
                ·
                  exact fin15Anchored_clause06738 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06739 chi hone hbad
                ·
                  exact fin15Anchored_clause06740 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06741 chi hone hbad
                ·
                  exact fin15Anchored_clause06742 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06743 chi hone hbad
                ·
                  exact fin15Anchored_clause06744 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06745 chi hone hbad
                ·
                  exact fin15Anchored_clause06746 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06747 chi hone hbad
                ·
                  exact fin15Anchored_clause06748 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06749 chi hone hbad
                ·
                  exact fin15Anchored_clause06750 chi hone hbad
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
                exact fin15Anchored_clause06751 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06752 chi hone hbad
                ·
                  exact fin15Anchored_clause06753 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06754 chi hone hbad
                ·
                  exact fin15Anchored_clause06755 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06756 chi hone hbad
                ·
                  exact fin15Anchored_clause06757 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06758 chi hone hbad
                ·
                  exact fin15Anchored_clause06759 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06760 chi hone hbad
                ·
                  exact fin15Anchored_clause06761 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06762 chi hone hbad
                ·
                  exact fin15Anchored_clause06763 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06764 chi hone hbad
                ·
                  exact fin15Anchored_clause06765 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06766 chi hone hbad
                ·
                  exact fin15Anchored_clause06767 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06768 chi hone hbad
                ·
                  exact fin15Anchored_clause06769 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06770 chi hone hbad
                ·
                  exact fin15Anchored_clause06771 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06772 chi hone hbad
                ·
                  exact fin15Anchored_clause06773 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06774 chi hone hbad
                ·
                  exact fin15Anchored_clause06775 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06776 chi hone hbad
                ·
                  exact fin15Anchored_clause06777 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06778 chi hone hbad
                ·
                  exact fin15Anchored_clause06779 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06780 chi hone hbad
                ·
                  exact fin15Anchored_clause06781 chi hone hbad
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
                  exact fin15Anchored_clause06782 chi hone hbad
                ·
                  exact fin15Anchored_clause06783 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06784 chi hone hbad
                ·
                  exact fin15Anchored_clause06785 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06786 chi hone hbad
                ·
                  exact fin15Anchored_clause06787 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06788 chi hone hbad
                ·
                  exact fin15Anchored_clause06789 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06790 chi hone hbad
                ·
                  exact fin15Anchored_clause06791 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06792 chi hone hbad
                ·
                  exact fin15Anchored_clause06793 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06794 chi hone hbad
                ·
                  exact fin15Anchored_clause06795 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06796 chi hone hbad
                ·
                  exact fin15Anchored_clause06797 chi hone hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06798 chi hone hbad
                ·
                  exact fin15Anchored_clause06799 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06800 chi hone hbad
                ·
                  exact fin15Anchored_clause06801 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06802 chi hone hbad
                ·
                  exact fin15Anchored_clause06803 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06804 chi hone hbad
                ·
                  exact fin15Anchored_clause06805 chi hone hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06806 chi hone hbad
                ·
                  exact fin15Anchored_clause06807 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06808 chi hone hbad
                ·
                  exact fin15Anchored_clause06809 chi hone hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06810 chi hone hbad
                ·
                  exact fin15Anchored_clause06811 chi hone hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause06812 chi hone hbad
                ·
                  exact fin15Anchored_clause06813 chi hone hbad

end ErdosSzekeres

end
