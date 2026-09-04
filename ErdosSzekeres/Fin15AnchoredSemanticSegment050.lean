module

public import ErdosSzekeres.Fin15AnchoredClauseChunk098
public import ErdosSzekeres.Fin15AnchoredClauseChunk099
public import ErdosSzekeres.Fin15AnchoredClauseChunk100

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 050. -/

theorem fin15Anchored_rejectSemanticSegment050
    (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ)
    (hanchor : chi.IsAnchored)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬Fin15AnchoredConclusion chi) :
    ¬(((((((((Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1475 chi) ∨
      ((Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1475 chi) ∨
      (¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1476 chi))) ∨
      (((¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1476 chi) ∨
      (Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1476 chi)) ∨
      ((¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1477 chi) ∨
      (¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1477 chi)))) ∨
      ((((¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1477 chi) ∨
      (Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1477 chi)) ∨
      ((Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1477 chi) ∨
      (¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1478 chi))) ∨
      (((¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi) ∨
      (¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1478 chi)) ∨
      ((¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi) ∨
      (¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi))))) ∨
      (((((Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi) ∨
      (Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi)) ∨
      ((Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1478 chi) ∨
      (Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi))) ∨
      (((Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1478 chi) ∨
      (¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1479 chi)) ∨
      ((¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi) ∨
      (¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1479 chi)))) ∨
      ((((¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi) ∨
      (¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi)) ∨
      ((Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi) ∨
      (Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi))) ∨
      (((Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1479 chi) ∨
      (Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi)) ∨
      ((Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1479 chi) ∨
      (¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1480 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi) ∨
      (¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1480 chi)) ∨
      ((¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi) ∨
      (¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi))) ∨
      (((Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi) ∨
      (Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1480 chi)) ∨
      ((Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi) ∨
      (Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1480 chi)))) ∨
      ((((¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1481 chi) ∨
      (¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi)) ∨
      ((¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1481 chi) ∨
      (¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi))) ∨
      (((¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi) ∨
      (Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi)) ∨
      ((Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi) ∨
      (Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1481 chi))))) ∨
      (((((Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi) ∨
      (Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1481 chi)) ∨
      ((¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1482 chi) ∨
      (¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1482 chi))) ∨
      (((¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1482 chi) ∨
      (¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1482 chi)) ∨
      ((Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1482 chi) ∨
      (Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1482 chi)))) ∨
      ((((Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1482 chi) ∨
      (Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1482 chi)) ∨
      ((Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1482 chi) ∨
      (¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1483 chi))) ∨
      (((¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1483 chi) ∨
      (Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1483 chi)) ∨
      ((¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) ∨
      ((¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi))) ∨
      (((¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi)) ∨
      ((Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1484 chi)))) ∨
      ((((Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) ∨
      (Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi)) ∨
      ((Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1484 chi) ∨
      (¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1485 chi))) ∨
      (((¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) ∨
      (¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi)) ∨
      ((¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1485 chi) ∨
      (¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi))))) ∨
      (((((¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) ∨
      (Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi)) ∨
      ((Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) ∨
      (Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1485 chi))) ∨
      (((Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) ∨
      (Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi)) ∨
      ((Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1485 chi) ∨
      (¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1486 chi)))) ∨
      ((((¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi) ∨
      (¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1486 chi)) ∨
      ((¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi) ∨
      (Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi))) ∨
      (((Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi) ∨
      (Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1486 chi)) ∨
      ((Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi) ∨
      (Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1486 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1487 chi) ∨
      (¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1487 chi)) ∨
      ((¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1487 chi) ∨
      (¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1487 chi))) ∨
      (((Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1487 chi) ∨
      (Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1487 chi)) ∨
      ((Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1487 chi) ∨
      (Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1487 chi)))) ∨
      ((((¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1488 chi) ∨
      (¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1488 chi)) ∨
      ((¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1488 chi) ∨
      (Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1488 chi))) ∨
      (((Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1488 chi) ∨
      (¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1489 chi)) ∨
      ((Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1489 chi) ∨
      (¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1490 chi))))) ∨
      (((((¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) ∨
      (¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi)) ∨
      ((¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1490 chi) ∨
      (¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi))) ∨
      (((Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) ∨
      (Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi)) ∨
      ((Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) ∨
      (Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1490 chi)))) ∨
      ((((Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) ∨
      (Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1490 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1491 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi))) ∨
      (((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1491 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi)))))))) ∨
      (((((((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1491 chi) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1491 chi))) ∨
      (((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1492 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1492 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1492 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1492 chi)))) ∨
      ((((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1492 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1492 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1492 chi))) ∨
      (((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1493 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1493 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi))))) ∨
      (((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1493 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1493 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1494 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi)))) ∨
      ((((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1494 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1494 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi)))))) ∨
      ((((((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1494 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1495 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1495 chi))) ∨
      (((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi)))) ∨
      ((((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1495 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1495 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1496 chi))) ∨
      (((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1496 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi))))) ∨
      (((((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1496 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1496 chi))) ∨
      (((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1497 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1497 chi)))) ∨
      ((((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1497 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1497 chi)) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1498 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi))))))) ∨
      ((((((¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1498 chi) ∨
      ((¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) ∨
      (¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi))) ∨
      (((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi)) ∨
      ((Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1498 chi)))) ∨
      ((((Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) ∨
      (Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1498 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1499 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi))) ∨
      (((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1499 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi))))) ∨
      (((((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1499 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1499 chi))) ∨
      (((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1500 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1500 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi)))) ∨
      ((((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1500 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1500 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1501 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi)))))) ∨
      ((((((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1501 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi))) ∨
      (((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1501 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1501 chi)))) ∨
      ((((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1502 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1502 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi))) ∨
      (((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1502 chi))))) ∨
      (((((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1503 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi))) ∨
      (((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1503 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi)))) ∨
      ((((Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1503 chi)) ∨
      ((Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi) ∨
      (Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1503 chi))) ∨
      (((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1504 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi)) ∨
      ((¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) ∨
      (¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1504 chi)))))))))) := by
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
                exact fin15Anchored_clause12619 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12620 chi hbad
                ·
                  exact fin15Anchored_clause12621 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12622 chi hbad
                ·
                  exact fin15Anchored_clause12623 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12624 chi hbad
                ·
                  exact fin15Anchored_clause12625 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12626 chi hbad
                ·
                  exact fin15Anchored_clause12627 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12628 chi hbad
                ·
                  exact fin15Anchored_clause12629 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12630 chi hbad
                ·
                  exact fin15Anchored_clause12631 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12632 chi hbad
                ·
                  exact fin15Anchored_clause12633 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12634 chi hbad
                ·
                  exact fin15Anchored_clause12635 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12636 chi hbad
                ·
                  exact fin15Anchored_clause12637 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12638 chi hbad
                ·
                  exact fin15Anchored_clause12639 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12640 chi hbad
                ·
                  exact fin15Anchored_clause12641 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12642 chi hbad
                ·
                  exact fin15Anchored_clause12643 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12644 chi hbad
                ·
                  exact fin15Anchored_clause12645 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12646 chi hbad
                ·
                  exact fin15Anchored_clause12647 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12648 chi hbad
                ·
                  exact fin15Anchored_clause12649 chi hbad
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
                  exact fin15Anchored_clause12650 chi hbad
                ·
                  exact fin15Anchored_clause12651 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12652 chi hbad
                ·
                  exact fin15Anchored_clause12653 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12654 chi hbad
                ·
                  exact fin15Anchored_clause12655 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12656 chi hbad
                ·
                  exact fin15Anchored_clause12657 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12658 chi hbad
                ·
                  exact fin15Anchored_clause12659 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12660 chi hbad
                ·
                  exact fin15Anchored_clause12661 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12662 chi hbad
                ·
                  exact fin15Anchored_clause12663 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12664 chi hbad
                ·
                  exact fin15Anchored_clause12665 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12666 chi hbad
                ·
                  exact fin15Anchored_clause12667 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12668 chi hbad
                ·
                  exact fin15Anchored_clause12669 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12670 chi hbad
                ·
                  exact fin15Anchored_clause12671 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12672 chi hbad
                ·
                  exact fin15Anchored_clause12673 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12674 chi hbad
                ·
                  exact fin15Anchored_clause12675 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12676 chi hbad
                ·
                  exact fin15Anchored_clause12677 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12678 chi hbad
                ·
                  exact fin15Anchored_clause12679 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12680 chi hbad
                ·
                  exact fin15Anchored_clause12681 chi hbad
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
                exact fin15Anchored_clause12682 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12683 chi hbad
                ·
                  exact fin15Anchored_clause12684 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12685 chi hbad
                ·
                  exact fin15Anchored_clause12686 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12687 chi hbad
                ·
                  exact fin15Anchored_clause12688 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12689 chi hbad
                ·
                  exact fin15Anchored_clause12690 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12691 chi hbad
                ·
                  exact fin15Anchored_clause12692 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12693 chi hbad
                ·
                  exact fin15Anchored_clause12694 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12695 chi hbad
                ·
                  exact fin15Anchored_clause12696 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12697 chi hbad
                ·
                  exact fin15Anchored_clause12698 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12699 chi hbad
                ·
                  exact fin15Anchored_clause12700 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12701 chi hbad
                ·
                  exact fin15Anchored_clause12702 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12703 chi hbad
                ·
                  exact fin15Anchored_clause12704 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12705 chi hbad
                ·
                  exact fin15Anchored_clause12706 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12707 chi hbad
                ·
                  exact fin15Anchored_clause12708 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12709 chi hbad
                ·
                  exact fin15Anchored_clause12710 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12711 chi hbad
                ·
                  exact fin15Anchored_clause12712 chi hbad
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
                  exact fin15Anchored_clause12713 chi hbad
                ·
                  exact fin15Anchored_clause12714 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12715 chi hbad
                ·
                  exact fin15Anchored_clause12716 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12717 chi hbad
                ·
                  exact fin15Anchored_clause12718 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12719 chi hbad
                ·
                  exact fin15Anchored_clause12720 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12721 chi hbad
                ·
                  exact fin15Anchored_clause12722 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12723 chi hbad
                ·
                  exact fin15Anchored_clause12724 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12725 chi hbad
                ·
                  exact fin15Anchored_clause12726 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12727 chi hbad
                ·
                  exact fin15Anchored_clause12728 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12729 chi hbad
                ·
                  exact fin15Anchored_clause12730 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12731 chi hbad
                ·
                  exact fin15Anchored_clause12732 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12733 chi hbad
                ·
                  exact fin15Anchored_clause12734 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12735 chi hbad
                ·
                  exact fin15Anchored_clause12736 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12737 chi hbad
                ·
                  exact fin15Anchored_clause12738 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12739 chi hbad
                ·
                  exact fin15Anchored_clause12740 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12741 chi hbad
                ·
                  exact fin15Anchored_clause12742 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12743 chi hbad
                ·
                  exact fin15Anchored_clause12744 chi hbad
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
                exact fin15Anchored_clause12745 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12746 chi hbad
                ·
                  exact fin15Anchored_clause12747 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12748 chi hbad
                ·
                  exact fin15Anchored_clause12749 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12750 chi hbad
                ·
                  exact fin15Anchored_clause12751 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12752 chi hbad
                ·
                  exact fin15Anchored_clause12753 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12754 chi hbad
                ·
                  exact fin15Anchored_clause12755 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12756 chi hbad
                ·
                  exact fin15Anchored_clause12757 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12758 chi hbad
                ·
                  exact fin15Anchored_clause12759 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12760 chi hbad
                ·
                  exact fin15Anchored_clause12761 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12762 chi hbad
                ·
                  exact fin15Anchored_clause12763 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12764 chi hbad
                ·
                  exact fin15Anchored_clause12765 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12766 chi hbad
                ·
                  exact fin15Anchored_clause12767 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12768 chi hbad
                ·
                  exact fin15Anchored_clause12769 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12770 chi hbad
                ·
                  exact fin15Anchored_clause12771 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12772 chi hbad
                ·
                  exact fin15Anchored_clause12773 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12774 chi hbad
                ·
                  exact fin15Anchored_clause12775 chi hbad
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
                  exact fin15Anchored_clause12776 chi hbad
                ·
                  exact fin15Anchored_clause12777 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12778 chi hbad
                ·
                  exact fin15Anchored_clause12779 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12780 chi hbad
                ·
                  exact fin15Anchored_clause12781 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12782 chi hbad
                ·
                  exact fin15Anchored_clause12783 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12784 chi hbad
                ·
                  exact fin15Anchored_clause12785 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12786 chi hbad
                ·
                  exact fin15Anchored_clause12787 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12788 chi hbad
                ·
                  exact fin15Anchored_clause12789 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12790 chi hbad
                ·
                  exact fin15Anchored_clause12791 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12792 chi hbad
                ·
                  exact fin15Anchored_clause12793 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12794 chi hbad
                ·
                  exact fin15Anchored_clause12795 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12796 chi hbad
                ·
                  exact fin15Anchored_clause12797 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12798 chi hbad
                ·
                  exact fin15Anchored_clause12799 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12800 chi hbad
                ·
                  exact fin15Anchored_clause12801 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12802 chi hbad
                ·
                  exact fin15Anchored_clause12803 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12804 chi hbad
                ·
                  exact fin15Anchored_clause12805 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12806 chi hbad
                ·
                  exact fin15Anchored_clause12807 chi hbad
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
                exact fin15Anchored_clause12808 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12809 chi hbad
                ·
                  exact fin15Anchored_clause12810 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12811 chi hbad
                ·
                  exact fin15Anchored_clause12812 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12813 chi hbad
                ·
                  exact fin15Anchored_clause12814 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12815 chi hbad
                ·
                  exact fin15Anchored_clause12816 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12817 chi hbad
                ·
                  exact fin15Anchored_clause12818 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12819 chi hbad
                ·
                  exact fin15Anchored_clause12820 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12821 chi hbad
                ·
                  exact fin15Anchored_clause12822 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12823 chi hbad
                ·
                  exact fin15Anchored_clause12824 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12825 chi hbad
                ·
                  exact fin15Anchored_clause12826 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12827 chi hbad
                ·
                  exact fin15Anchored_clause12828 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12829 chi hbad
                ·
                  exact fin15Anchored_clause12830 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12831 chi hbad
                ·
                  exact fin15Anchored_clause12832 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12833 chi hbad
                ·
                  exact fin15Anchored_clause12834 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12835 chi hbad
                ·
                  exact fin15Anchored_clause12836 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12837 chi hbad
                ·
                  exact fin15Anchored_clause12838 chi hbad
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
                  exact fin15Anchored_clause12839 chi hbad
                ·
                  exact fin15Anchored_clause12840 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12841 chi hbad
                ·
                  exact fin15Anchored_clause12842 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12843 chi hbad
                ·
                  exact fin15Anchored_clause12844 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12845 chi hbad
                ·
                  exact fin15Anchored_clause12846 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12847 chi hbad
                ·
                  exact fin15Anchored_clause12848 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12849 chi hbad
                ·
                  exact fin15Anchored_clause12850 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12851 chi hbad
                ·
                  exact fin15Anchored_clause12852 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12853 chi hbad
                ·
                  exact fin15Anchored_clause12854 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12855 chi hbad
                ·
                  exact fin15Anchored_clause12856 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12857 chi hbad
                ·
                  exact fin15Anchored_clause12858 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12859 chi hbad
                ·
                  exact fin15Anchored_clause12860 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12861 chi hbad
                ·
                  exact fin15Anchored_clause12862 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12863 chi hbad
                ·
                  exact fin15Anchored_clause12864 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12865 chi hbad
                ·
                  exact fin15Anchored_clause12866 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12867 chi hbad
                ·
                  exact fin15Anchored_clause12868 chi hbad
              ·
                rcases hbad with hbad | hbad
                ·
                  exact fin15Anchored_clause12869 chi hbad
                ·
                  exact fin15Anchored_clause12870 chi hbad

end ErdosSzekeres

end
