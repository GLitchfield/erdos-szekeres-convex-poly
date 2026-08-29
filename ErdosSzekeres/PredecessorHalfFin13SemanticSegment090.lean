module

public import ErdosSzekeres.PredecessorHalfFin13ClauseChunk069

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Semantic rejection of balanced CNF subtree 090. -/

theorem predecessorHalfFin13_rejectSemanticSegment090
    (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ)
    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)
    (hno : ¬PredecessorHalfFin13Conclusion chi) :
    ¬((((((((PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) ∨
      ((PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) ∨
      (PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi))) ∨
      ((PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) ∨
      ((PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) ∨
      (PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1431 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0936 chi) ∨
      ((PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) ∨
      (PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi))) ∨
      ((PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) ∨
      ((PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) ∨
      (PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi))))) ∨
      ((((¬PredecessorHalfFin13Atom1432 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0937 chi) ∨
      ((PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) ∨
      (PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi))) ∨
      ((PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) ∨
      ((PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) ∨
      (PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi)))) ∨
      (((¬PredecessorHalfFin13Atom1433 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0938 chi) ∨
      ((PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) ∨
      (PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi))) ∨
      ((PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      ((PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) ∨
      (PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi)))))) ∨
      (((((¬PredecessorHalfFin13Atom1435 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0940 chi) ∨
      ((PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) ∨
      (PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi))) ∨
      ((PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) ∨
      ((PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) ∨
      (PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi)))) ∨
      (((PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) ∨
      ((PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) ∨
      (PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi))) ∨
      ((PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) ∨
      ((PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) ∨
      (¬PredecessorHalfFin13Atom1438 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0943 chi))))) ∨
      ((((PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) ∨
      ((PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) ∨
      (PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi))) ∨
      ((PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) ∨
      ((PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) ∨
      (PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi)))) ∨
      (((PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) ∨
      ((PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) ∨
      (PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi))) ∨
      (((PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) ∨
      (¬PredecessorHalfFin13Atom1442 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0947 chi)) ∨
      ((PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) ∨
      (PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi))))))) ∨
      ((((((PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) ∨
      ((PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) ∨
      (PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi))) ∨
      ((¬PredecessorHalfFin13Atom1443 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0948 chi) ∨
      ((PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) ∨
      (PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi)))) ∨
      (((PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      ((PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) ∨
      (PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi))) ∨
      ((¬PredecessorHalfFin13Atom1445 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0950 chi) ∨
      ((PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) ∨
      (PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi))))) ∨
      ((((PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) ∨
      ((PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) ∨
      (PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi))) ∨
      ((¬PredecessorHalfFin13Atom1446 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0951 chi) ∨
      ((PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) ∨
      (PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi)))) ∨
      (((PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) ∨
      ((PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) ∨
      (PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi))) ∨
      ((¬PredecessorHalfFin13Atom1448 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0953 chi) ∨
      ((PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) ∨
      (PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi)))))) ∨
      (((((PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) ∨
      ((PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) ∨
      (PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi))) ∨
      ((PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) ∨
      ((PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) ∨
      (PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi)))) ∨
      (((PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) ∨
      ((PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) ∨
      (PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi))) ∨
      ((PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      ((PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) ∨
      (PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi))))) ∨
      ((((PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) ∨
      ((¬PredecessorHalfFin13Atom1454 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0959 chi) ∨
      (PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi))) ∨
      ((PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) ∨
      ((PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) ∨
      (PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi)))) ∨
      (((PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) ∨
      ((¬PredecessorHalfFin13Atom1456 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0961 chi) ∨
      (PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi))) ∨
      (((PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) ∨
      (PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi)) ∨
      ((PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) ∨
      (PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi))))))))) := by
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
              exact predecessorHalfFin13_clause19727 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19735 chi hbad
              ·
                exact predecessorHalfFin13_clause19736 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19737 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19738 chi hbad
              ·
                exact predecessorHalfFin13_clause19739 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19740 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19741 chi hbad
              ·
                exact predecessorHalfFin13_clause19742 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19743 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19744 chi hbad
              ·
                exact predecessorHalfFin13_clause19745 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19746 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19747 chi hbad
              ·
                exact predecessorHalfFin13_clause19748 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19749 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19750 chi hbad
              ·
                exact predecessorHalfFin13_clause19751 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19752 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19759 chi hbad
              ·
                exact predecessorHalfFin13_clause19760 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19761 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19762 chi hbad
              ·
                exact predecessorHalfFin13_clause19763 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19764 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19765 chi hbad
              ·
                exact predecessorHalfFin13_clause19766 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19767 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19768 chi hbad
              ·
                exact predecessorHalfFin13_clause19769 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19777 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19778 chi hbad
              ·
                exact predecessorHalfFin13_clause19779 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19780 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19781 chi hbad
              ·
                exact predecessorHalfFin13_clause19782 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19789 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19790 chi hbad
              ·
                exact predecessorHalfFin13_clause19791 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19792 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19793 chi hbad
              ·
                exact predecessorHalfFin13_clause19801 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19802 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19803 chi hbad
              ·
                exact predecessorHalfFin13_clause19804 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19805 chi hbad
              ·
                exact predecessorHalfFin13_clause19806 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19807 chi hbad
              ·
                exact predecessorHalfFin13_clause19808 chi hbad
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
              exact predecessorHalfFin13_clause19809 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19810 chi hbad
              ·
                exact predecessorHalfFin13_clause19811 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19812 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19819 chi hbad
              ·
                exact predecessorHalfFin13_clause19820 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19821 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19822 chi hbad
              ·
                exact predecessorHalfFin13_clause19823 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19824 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19825 chi hbad
              ·
                exact predecessorHalfFin13_clause19826 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19827 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19828 chi hbad
              ·
                exact predecessorHalfFin13_clause19829 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19830 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19837 chi hbad
              ·
                exact predecessorHalfFin13_clause19838 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19839 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19840 chi hbad
              ·
                exact predecessorHalfFin13_clause19841 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19842 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19849 chi hbad
              ·
                exact predecessorHalfFin13_clause19850 chi hbad
    ·
      rcases hbad with hbad | hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19851 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19852 chi hbad
              ·
                exact predecessorHalfFin13_clause19853 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19861 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19862 chi hbad
              ·
                exact predecessorHalfFin13_clause19863 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19864 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19865 chi hbad
              ·
                exact predecessorHalfFin13_clause19873 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19874 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19875 chi hbad
              ·
                exact predecessorHalfFin13_clause19876 chi hbad
      ·
        rcases hbad with hbad | hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19877 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19878 chi hbad
              ·
                exact predecessorHalfFin13_clause19885 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19886 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19887 chi hbad
              ·
                exact predecessorHalfFin13_clause19888 chi hbad
        ·
          rcases hbad with hbad | hbad
          ·
            rcases hbad with hbad | hbad
            ·
              exact predecessorHalfFin13_clause19889 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19890 chi hbad
              ·
                exact predecessorHalfFin13_clause19903 chi hbad
          ·
            rcases hbad with hbad | hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19904 chi hbad
              ·
                exact predecessorHalfFin13_clause19905 chi hbad
            ·
              rcases hbad with hbad | hbad
              ·
                exact predecessorHalfFin13_clause19906 chi hbad
              ·
                exact predecessorHalfFin13_clause19907 chi hbad

end ErdosSzekeres

end
