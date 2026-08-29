module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk068
public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk069

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 089. -/

theorem predecessorHalfFin13_rejectSemanticSegment089
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0431 chi) ∨
      ((PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) ∨
      (PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi))) ∨
      ((PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) ∨
      ((PredecessorHalfFin13Atom1400 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) ∨
      (¬PredecessorHalfFin13Atom1400 chi ∧
      PredecessorHalfFin13Atom0431 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0905 chi)))) ∨
      (((PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) ∨
      ((PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) ∨
      (PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi))) ∨
      ((PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) ∨
      ((PredecessorHalfFin13Atom1401 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) ∨
      (¬PredecessorHalfFin13Atom1401 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0481 chi ∧
      PredecessorHalfFin13Atom0906 chi))))) ∨
      ((((PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0432 chi) ∨
      ((PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) ∨
      (PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi))) ∨
      ((PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) ∨
      ((PredecessorHalfFin13Atom1403 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) ∨
      (¬PredecessorHalfFin13Atom1403 chi ∧
      PredecessorHalfFin13Atom0432 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0908 chi)))) ∨
      (((PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0433 chi) ∨
      ((PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0435 chi) ∨
      (PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi))) ∨
      ((PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) ∨
      ((PredecessorHalfFin13Atom1405 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) ∨
      (¬PredecessorHalfFin13Atom1405 chi ∧
      PredecessorHalfFin13Atom0433 chi ∧
      PredecessorHalfFin13Atom0435 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0485 chi ∧
      PredecessorHalfFin13Atom0910 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) ∨
      ((PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) ∨
      (PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi))) ∨
      ((PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) ∨
      ((PredecessorHalfFin13Atom1407 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) ∨
      (¬PredecessorHalfFin13Atom1407 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0912 chi)))) ∨
      (((PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) ∨
      ((PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) ∨
      (PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi))) ∨
      ((PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) ∨
      ((PredecessorHalfFin13Atom1408 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) ∨
      (¬PredecessorHalfFin13Atom1408 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0913 chi))))) ∨
      ((((PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0436 chi) ∨
      ((PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) ∨
      (PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi))) ∨
      ((PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) ∨
      ((PredecessorHalfFin13Atom1410 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) ∨
      (¬PredecessorHalfFin13Atom1410 chi ∧
      PredecessorHalfFin13Atom0436 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0915 chi)))) ∨
      (((PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi) ∨
      ((PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi) ∨
      (PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi))) ∨
      (((PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      (PredecessorHalfFin13Atom1411 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi)) ∨
      ((¬PredecessorHalfFin13Atom1411 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0916 chi) ∨
      (PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0437 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) ∨
      ((PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) ∨
      (PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi))) ∨
      ((PredecessorHalfFin13Atom1413 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) ∨
      ((¬PredecessorHalfFin13Atom1413 chi ∧
      PredecessorHalfFin13Atom0437 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0918 chi) ∨
      (PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0438 chi)))) ∨
      (((PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0440 chi) ∨
      ((PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) ∨
      (PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi))) ∨
      ((PredecessorHalfFin13Atom1415 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) ∨
      ((¬PredecessorHalfFin13Atom1415 chi ∧
      PredecessorHalfFin13Atom0438 chi ∧
      PredecessorHalfFin13Atom0440 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0495 chi ∧
      PredecessorHalfFin13Atom0920 chi) ∨
      (PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi))))) ∨
      ((((PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) ∨
      ((PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) ∨
      (PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi))) ∨
      ((PredecessorHalfFin13Atom1417 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) ∨
      ((PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0441 chi) ∨
      (PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi)))) ∨
      (((PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi) ∨
      ((PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) ∨
      (PredecessorHalfFin13Atom1419 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi))) ∨
      ((¬PredecessorHalfFin13Atom1419 chi ∧
      PredecessorHalfFin13Atom0441 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0924 chi) ∨
      ((PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0442 chi) ∨
      (PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0444 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) ∨
      ((PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) ∨
      (PredecessorHalfFin13Atom1421 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi))) ∨
      ((¬PredecessorHalfFin13Atom1421 chi ∧
      PredecessorHalfFin13Atom0442 chi ∧
      PredecessorHalfFin13Atom0444 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0926 chi) ∨
      ((PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0445 chi) ∨
      (PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0447 chi)))) ∨
      (((PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0449 chi) ∨
      ((PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) ∨
      (PredecessorHalfFin13Atom1424 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi))) ∨
      ((¬PredecessorHalfFin13Atom1424 chi ∧
      PredecessorHalfFin13Atom0445 chi ∧
      PredecessorHalfFin13Atom0447 chi ∧
      PredecessorHalfFin13Atom0449 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0929 chi) ∨
      ((PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) ∨
      (PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi))))) ∨
      ((((PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) ∨
      ((PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) ∨
      (PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi))) ∨
      ((PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) ∨
      ((PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) ∨
      (PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi)))) ∨
      (((PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) ∨
      ((PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) ∨
      (¬PredecessorHalfFin13Atom1428 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0933 chi))) ∨
      (((PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) ∨
      (PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi)) ∨
      ((PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) ∨
      (PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi))))))))) := by
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
              exact predecessorHalfFin13_clause19549 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19550 chi hbad
              ·
                exact predecessorHalfFin13_clause19551 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19552 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19553 chi hbad
              ·
                exact predecessorHalfFin13_clause19554 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19555 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19556 chi hbad
              ·
                exact predecessorHalfFin13_clause19557 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19558 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19559 chi hbad
              ·
                exact predecessorHalfFin13_clause19560 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19567 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19568 chi hbad
              ·
                exact predecessorHalfFin13_clause19569 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19570 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19571 chi hbad
              ·
                exact predecessorHalfFin13_clause19572 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19579 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19580 chi hbad
              ·
                exact predecessorHalfFin13_clause19581 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19582 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19583 chi hbad
              ·
                exact predecessorHalfFin13_clause19584 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19591 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19592 chi hbad
              ·
                exact predecessorHalfFin13_clause19593 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19594 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19595 chi hbad
              ·
                exact predecessorHalfFin13_clause19596 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19597 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19598 chi hbad
              ·
                exact predecessorHalfFin13_clause19599 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19600 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19601 chi hbad
              ·
                exact predecessorHalfFin13_clause19602 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19609 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19610 chi hbad
              ·
                exact predecessorHalfFin13_clause19611 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19612 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19613 chi hbad
              ·
                exact predecessorHalfFin13_clause19614 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19615 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19616 chi hbad
              ·
                exact predecessorHalfFin13_clause19617 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19618 chi hbad
              ·
                exact predecessorHalfFin13_clause19619 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19620 chi hbad
              ·
                exact predecessorHalfFin13_clause19627 chi hbad
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
              exact predecessorHalfFin13_clause19628 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19629 chi hbad
              ·
                exact predecessorHalfFin13_clause19630 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19631 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19632 chi hbad
              ·
                exact predecessorHalfFin13_clause19639 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19640 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19641 chi hbad
              ·
                exact predecessorHalfFin13_clause19642 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19643 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19644 chi hbad
              ·
                exact predecessorHalfFin13_clause19651 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19652 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19653 chi hbad
              ·
                exact predecessorHalfFin13_clause19654 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19655 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19663 chi hbad
              ·
                exact predecessorHalfFin13_clause19664 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19665 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19666 chi hbad
              ·
                exact predecessorHalfFin13_clause19667 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19668 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19675 chi hbad
              ·
                exact predecessorHalfFin13_clause19676 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19677 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19678 chi hbad
              ·
                exact predecessorHalfFin13_clause19679 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19680 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19693 chi hbad
              ·
                exact predecessorHalfFin13_clause19694 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19695 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19696 chi hbad
              ·
                exact predecessorHalfFin13_clause19697 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19698 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19711 chi hbad
              ·
                exact predecessorHalfFin13_clause19712 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19713 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19714 chi hbad
              ·
                exact predecessorHalfFin13_clause19715 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19717 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19718 chi hbad
              ·
                exact predecessorHalfFin13_clause19719 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19720 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19721 chi hbad
              ·
                exact predecessorHalfFin13_clause19722 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19723 chi hbad
              ·
                exact predecessorHalfFin13_clause19724 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19725 chi hbad
              ·
                exact predecessorHalfFin13_clause19726 chi hbad

end ErdosSzekeres

end
